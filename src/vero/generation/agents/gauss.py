"""OpenGauss (`gauss`) agent — ``gauss chat -q …`` subprocess, plaintext stdout.

Built on :class:`BaseAgent`, so it shares persistent logging + error handling
+ timeout plumbing with :class:`ClaudeAgent`, :class:`CodexAgent`, and
:class:`GeminiAgent`.

OpenGauss's ``gauss chat`` does not emit a JSON event stream (only plaintext
to stdout). We log the full stdout as canonical ``text`` events, stream-line
buffered. The CLI does not accept a ``--save-trajectories`` flag as of v0.2.2
(it is SDK-only), so the trajectory-replay code path is inert for normal
``gauss chat`` runs; a file at ``<sandbox>/gauss_trajectory.jsonl`` dropped
in by something else (SDK integration, future CLI flag) will still get
parsed.

Per-sandbox isolation: ``GAUSS_HOME=<sandbox>/.gauss_home`` relocates the
entire ``~/.gauss/`` tree (config, .env, auth.json, gateway PID file) — so
multiple installations can run concurrently and the user's login is untouched.

Credential fallback uses a per-provider map since gauss sits above many
providers. Fallback chain (first non-empty wins):

- ``api_key``: ``GAUSS_AGENT_API_KEY`` → ``LLM_API_KEY`` →
  ``<provider-specific env var>``
- ``base_url``: ``GAUSS_AGENT_BASE_URL`` → ``LLM_API_BASE``

Provider → env-var map:

- ``auto`` / ``openrouter`` → ``OPENROUTER_API_KEY``
- ``anthropic`` → ``ANTHROPIC_API_KEY``
- ``openai-codex`` → ``OPENAI_API_KEY``
- ``zai`` → ``GLM_API_KEY``
- ``kimi-coding`` → ``KIMI_API_KEY``
- ``minimax`` / ``minimax-cn`` → ``MINIMAX_API_KEY``
- ``nous`` → ``NOUS_API_KEY``

The resolved values are written into ``$GAUSS_HOME/.env`` before spawn (gauss
auto-loads that file). ``OPENAI_BASE_URL`` is also recorded when a base URL is
resolved — gauss documents that key for the local-vLLM / LiteLLM proxy path.

The prompt given to ``gauss chat -q`` is the contents of INSTRUCTION.md plus
an in-agent nudge telling gauss it may use its ``/prove``, ``/autoformalize``
slash commands if it helps. The shared INSTRUCTION templates stay unchanged —
this nudge is gauss-specific and applied at runtime.
"""

from __future__ import annotations

import json
import os
import shutil
import subprocess
import threading
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from vero.generation.agents.base import BaseAgent, RunOutcome
from vero.generation.agents.event_log import EventLogger

_GAUSS_BIN = "gauss"
_GAUSS_HOME_DIRNAME = ".gauss_home"
_TRAJECTORY_FILENAME = "gauss_trajectory.jsonl"

_PROVIDER_ENV_KEY: dict[str, str] = {
    "auto": "OPENROUTER_API_KEY",
    "openrouter": "OPENROUTER_API_KEY",
    "anthropic": "ANTHROPIC_API_KEY",
    "openai-codex": "OPENAI_API_KEY",
    "zai": "GLM_API_KEY",
    "kimi-coding": "KIMI_API_KEY",
    "minimax": "MINIMAX_API_KEY",
    "minimax-cn": "MINIMAX_API_KEY",
    "nous": "NOUS_API_KEY",
}

_GAUSS_NUDGE = (
    "\n\n---\n\n"
    "You are running inside the `gauss` agent. The Lean tooling and MCP "
    "scaffolding are already wired. You may invoke gauss's slash commands "
    "(`/prove`, `/autoformalize`, `/formalize`, `/golf`, `/review`, "
    "`/checkpoint`) if they help — or do the work directly by editing "
    "marker interiors. Either is fine.\n"
)


def _resolve_creds(provider: str) -> tuple[str | None, str | None]:
    """Resolve gauss API key + base URL.

    First non-empty wins:

    - ``api_key``: ``GAUSS_AGENT_API_KEY`` → ``LLM_API_KEY`` →
      ``<provider-specific env var>``
    - ``base_url``: ``GAUSS_AGENT_BASE_URL`` → ``LLM_API_BASE``
    """
    provider_key_name = _PROVIDER_ENV_KEY.get(provider, "OPENROUTER_API_KEY")
    api_key = (
        os.getenv("GAUSS_AGENT_API_KEY")
        or os.getenv("LLM_API_KEY")
        or os.getenv(provider_key_name)
        or None
    )
    base_url = os.getenv("GAUSS_AGENT_BASE_URL") or os.getenv("LLM_API_BASE") or None
    return api_key, base_url


@dataclass
class GaussAgent(BaseAgent):
    """Headless OpenGauss runner."""

    provider: str = "auto"
    model: str | None = None
    # Which CLI gauss delegates Lean slash commands to: "claude-code" | "codex".
    backend: str = "claude-code"
    timeout_seconds: int = 1800
    yolo: bool = True
    worktree: bool = False
    # Reserved for forward-compatibility with a future CLI `--save-trajectories`
    # flag. The v0.2.2 CLI has no such flag (only the Python SDK supports it),
    # so setting this to True does not change the command line today — we
    # simply look for the file on exit and replay it if present.
    save_trajectories: bool = False
    name: str = "gauss"

    def _run_start_payload(self) -> dict[str, Any]:
        return {
            "agent": self.name,
            "provider": self.provider,
            "model": self.model,
            "backend": self.backend,
            "timeout_seconds": self.timeout_seconds,
            "yolo": self.yolo,
            "worktree": self.worktree,
            "save_trajectories": self.save_trajectories,
        }

    # ─── build_cmd ────────────────────────────────────────────────

    def _build_cmd(self, prompt: str) -> list[str]:
        cmd = [
            _GAUSS_BIN,
            "chat",
            "-q",
            prompt,
            "--quiet",
            "--provider",
            self.provider,
        ]
        if self.yolo:
            cmd.append("--yolo")
        if self.model:
            cmd.extend(["-m", self.model])
        if self.worktree:
            cmd.append("--worktree")
        # NOTE: no --save-trajectories flag on `gauss chat` v0.2.2; replay
        # happens post-run if the file materializes via some other means.
        return cmd

    # ─── build_prompt ─────────────────────────────────────────────

    def _build_prompt(self, instruction_text: str) -> str:
        return instruction_text + _GAUSS_NUDGE

    # ─── prepare_gauss_home ───────────────────────────────────────

    def _prepare_gauss_home(self, sandbox_dir: Path, event_log: EventLogger) -> Path:
        """Create ``<sandbox>/.gauss_home`` and write a minimal ``.env``.

        The ``.env`` file is auto-loaded by gauss. We only write the keys we
        resolved — if the caller already has a ``~/.gauss/.env`` but wants
        this run to use different creds, ``GAUSS_HOME`` redirects everything.
        """
        home = sandbox_dir / _GAUSS_HOME_DIRNAME
        home.mkdir(parents=True, exist_ok=True)

        api_key, base_url = _resolve_creds(self.provider)
        provider_key_name = _PROVIDER_ENV_KEY.get(self.provider, "OPENROUTER_API_KEY")

        env_lines: list[str] = []
        if api_key:
            env_lines.append(f"{provider_key_name}={api_key}")
        if base_url:
            # Gauss uses OPENAI_BASE_URL for local-vLLM / LiteLLM routing.
            env_lines.append(f"OPENAI_BASE_URL={base_url}")
        (home / ".env").write_text("\n".join(env_lines) + "\n", encoding="utf-8")

        event_log.raw(
            ev="gauss_home_prepared",
            path=str(home),
            provider=self.provider,
            has_api_key=bool(api_key),
            has_base_url=bool(base_url),
        )
        return home

    # ─── prepare_env ──────────────────────────────────────────────

    def _prepare_env(self, gauss_home: Path) -> dict[str, str]:
        env = os.environ.copy()
        env["GAUSS_HOME"] = str(gauss_home)
        # Scrub claude-code vars — gauss may spawn `claude` internally when
        # backend=claude-code; the nested CLI would otherwise refuse to
        # launch inside an active Claude Code session.
        for k in ("CLAUDECODE", "CLAUDE_CODE_ENTRYPOINT", "CLAUDE_CODE_SSE_PORT"):
            env.pop(k, None)
        return env

    # ─── require_binary ───────────────────────────────────────────

    def _require_binary(self, event_log: EventLogger) -> None:
        if shutil.which(_GAUSS_BIN) is None:
            event_log.error(
                "gauss binary not on PATH; install from "
                "https://github.com/math-inc/OpenGauss",
                binary=_GAUSS_BIN,
            )
            raise FileNotFoundError(f"`{_GAUSS_BIN}` not found on PATH")
        backend_bin = "claude" if self.backend == "claude-code" else "codex"
        if shutil.which(backend_bin) is None:
            event_log.error(
                f"gauss backend={self.backend!r} requires `{backend_bin}` "
                "on PATH; install it or switch the backend config.",
                binary=backend_bin,
            )
            raise FileNotFoundError(f"`{backend_bin}` not found on PATH")

    # ─── trajectory replay ────────────────────────────────────────

    def _replay_trajectory(self, path: Path, event_log: EventLogger) -> None:
        """Parse a ShareGPT JSONL trajectory into canonical events.

        Gauss writes one JSONL line per conversation. We take the last line
        (most relevant for single-prompt runs) and translate each ``{from,
        value}`` turn into a ``text`` / ``tool_use`` / ``raw`` event. This is
        best-effort post-analysis; failures are logged but don't fail the run.
        """
        if not path.is_file():
            return
        try:
            text = path.read_text(encoding="utf-8").strip()
            if not text:
                return
            last = text.splitlines()[-1]
            traj = json.loads(last)
        except (OSError, json.JSONDecodeError) as e:
            event_log.raw(ev="gauss_trajectory_parse_failed", error=str(e))
            return
        for turn in traj.get("conversations", []):
            role = turn.get("from")
            body = turn.get("value", "")
            if role == "gpt":
                event_log.text(body)
            elif role == "tool":
                event_log.tool_use(name="gauss_tool", input=body, id=None)
            else:
                event_log.raw(ev="gauss_trajectory_turn", role=role, value=body)

    # ─── run_inner ────────────────────────────────────────────────

    def _run_inner(
        self,
        *,
        event_log: EventLogger,
        sandbox_dir: Path,
        instruction_file: Path,
    ) -> RunOutcome:
        self._require_binary(event_log)

        gauss_home = self._prepare_gauss_home(sandbox_dir, event_log)
        env = self._prepare_env(gauss_home)

        instruction_text = instruction_file.read_text(encoding="utf-8")
        prompt = self._build_prompt(instruction_text)

        cmd = self._build_cmd(prompt=prompt)
        trajectory_path = sandbox_dir / _TRAJECTORY_FILENAME

        event_log.raw(
            ev="gauss_cmd",
            # Don't echo the full prompt in the cmd line — it can be huge.
            cmd=[
                c if i != cmd.index("-q") + 1 else "(+prompt)"
                for i, c in enumerate(cmd)
            ],
            cwd=str(sandbox_dir),
            gauss_home=str(gauss_home),
            trajectory_path=str(trajectory_path),
            prompt_bytes=len(prompt.encode("utf-8")),
        )

        outcome = self._spawn_and_stream(
            cmd=cmd, cwd=sandbox_dir, env=env, event_log=event_log
        )

        # Best-effort replay if something (SDK, future CLI flag, user script)
        # dropped a ShareGPT JSONL file at the conventional path.
        self._replay_trajectory(trajectory_path, event_log)

        return outcome

    # ─── spawn + stream ───────────────────────────────────────────

    def _spawn_and_stream(
        self,
        *,
        cmd: list[str],
        cwd: Path,
        env: dict[str, str],
        event_log: EventLogger,
    ) -> RunOutcome:
        proc = subprocess.Popen(
            cmd,
            cwd=str(cwd),
            env=env,
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            bufsize=1,
        )

        killed = {"by_timeout": False}

        def _kill() -> None:
            killed["by_timeout"] = True
            try:
                proc.terminate()
            except ProcessLookupError:
                pass

        timer = threading.Timer(self.timeout_seconds, _kill)
        timer.daemon = True
        timer.start()

        state: dict[str, Any] = {
            "ok": True,
            "last_error": None,
        }

        stderr_chunks: list[str] = []

        def _drain_stderr() -> None:
            assert proc.stderr is not None
            for line in proc.stderr:
                stderr_chunks.append(line)
                stripped = line.rstrip("\n")
                if not stripped:
                    continue
                try:
                    event_log.raw(ev="gauss_stderr", line=stripped)
                except ValueError:
                    # Parent may have closed the log file if join(timeout=2)
                    # timed out — drop the line rather than crash.
                    break

        stderr_thread = threading.Thread(target=_drain_stderr, daemon=True)
        stderr_thread.start()

        assert proc.stdout is not None
        text_lines: list[str] = []
        for raw_line in proc.stdout:
            line = raw_line.rstrip("\n")
            if not line:
                continue
            text_lines.append(line)
        # Gauss's plaintext stream is conversational; flush the whole block
        # as one text event so the human-readable log stays scannable. The
        # JSONL mirror keeps it verbatim.
        if text_lines:
            event_log.text("\n".join(text_lines))

        exit_code = proc.wait()
        timer.cancel()
        stderr_thread.join(timeout=2)

        if killed["by_timeout"]:
            state["ok"] = False
            state["last_error"] = (
                f"gauss exceeded {self.timeout_seconds}s and was terminated"
            )

        if exit_code != 0 and state["ok"]:
            state["ok"] = False
            state["last_error"] = f"gauss exit={exit_code}"

        event_log.raw(
            ev="gauss_exit",
            exit_code=exit_code,
            killed_by_timeout=killed["by_timeout"],
        )
        # Gauss does not emit per-invocation usage; surface this clearly in
        # the log so downstream analysis doesn't expect numbers.
        event_log.raw(ev="gauss_usage_unknown")

        stderr_tail = "".join(stderr_chunks)[-2000:] if stderr_chunks else None

        return RunOutcome(
            ok=state["ok"],
            num_turns=0,  # plaintext stream; no reliable per-turn signal
            total_cost_usd=None,
            usage={},
            stderr_tail=stderr_tail,
            error=state["last_error"] if not state["ok"] else None,
            extra={"exit_code": exit_code},
        )
