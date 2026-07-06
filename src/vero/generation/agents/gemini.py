"""Gemini CLI agent — ``gemini -p … --output-format stream-json`` scoped to a sandbox.

Built on :class:`BaseAgent` so it shares persistent logging + error
handling + timeout plumbing with :class:`ClaudeAgent` and :class:`CodexAgent`.

The Gemini CLI's headless mode emits one JSON envelope per stdout line when
``--output-format stream-json`` is set (``init | message | tool_use | tool_result
| error | result``). We route those into our canonical event kinds. The final
``result`` envelope carries aggregated per-model token usage — we populate
``RunOutcome.usage`` from it. No dollar cost is emitted (same as codex).

Per-sandbox isolation uses ``GEMINI_CLI_HOME`` which relocates the entire
``.gemini/`` tree (settings, OAuth cache, session store) — so a benchmark run
never touches the user's login.

Credential resolution is LiteLLM-first (so ``.env`` loaded by the CLI entry
just works). Fallback chain:

- ``api_key``: ``GEMINI_AGENT_API_KEY`` → ``LLM_API_KEY`` → ``GEMINI_API_KEY``
  → ``GOOGLE_API_KEY``
- ``base_url``: ``GEMINI_AGENT_BASE_URL`` → ``LLM_API_BASE``
  → ``GOOGLE_GEMINI_BASE_URL``

The resolved values are injected as ``GEMINI_API_KEY`` + ``GOOGLE_GEMINI_BASE_URL``
in the subprocess env (the shape the CLI actually reads).
"""

from __future__ import annotations

import json
import os
import shutil
import subprocess
import threading
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

from vero.generation.agents.base import BaseAgent, RunOutcome
from vero.generation.agents.event_log import EventLogger

_GEMINI_BIN = "gemini"
_GEMINI_HOME_DIRNAME = ".gemini_home"

# Prompts larger than this are piped via stdin instead of the -p flag to
# stay under platform ARG_MAX. 100 KB is well under the Linux 128 KB
# minimum while also being far above any realistic INSTRUCTION.md.
_PROMPT_ARG_MAX_BYTES = 100_000


def _resolve_creds() -> tuple[str | None, str | None]:
    """Resolve Gemini API key + base URL. LiteLLM-first fallback chain.

    Empty strings are treated as unset, matching codex's resolver.
    """
    api_key = (
        os.getenv("GEMINI_AGENT_API_KEY")
        or os.getenv("LLM_API_KEY")
        or os.getenv("GEMINI_API_KEY")
        or os.getenv("GOOGLE_API_KEY")
        or None
    )
    base_url = (
        os.getenv("GEMINI_AGENT_BASE_URL")
        or os.getenv("LLM_API_BASE")
        or os.getenv("GOOGLE_GEMINI_BASE_URL")
        or None
    )
    return api_key, base_url


@dataclass
class GeminiAgent(BaseAgent):
    """Headless gemini-cli runner."""

    model: str = "gemini-3.1-pro-preview"
    # "off" | "docker" | "podman" | "seatbelt" — "off" omits --sandbox entirely
    sandbox_mode: str = "off"
    # yolo | auto_edit | default | plan (yolo is what the CLI actually wants
    # for non-interactive runs; --yolo is the deprecated alias)
    approval_mode: str = "yolo"
    timeout_seconds: int = 1800
    name: str = "gemini"
    # Reserved for future settings.json injection (e.g. tools.core, allowed-tools
    # policy). Not wired into the CLI as -c flags.
    config_overrides: list[str] = field(default_factory=list)

    def _run_start_payload(self) -> dict[str, Any]:
        return {
            "agent": self.name,
            "model": self.model,
            "sandbox_mode": self.sandbox_mode,
            "approval_mode": self.approval_mode,
            "timeout_seconds": self.timeout_seconds,
        }

    # ─── build_cmd ────────────────────────────────────────────────

    def _build_cmd(self) -> list[str]:
        cmd = [
            _GEMINI_BIN,
            "--output-format",
            "stream-json",
            "--approval-mode",
            self.approval_mode,
        ]
        # The real CLI's -s/--sandbox is a boolean switch; the backend
        # (docker/podman/seatbelt/…) is chosen by the GEMINI_SANDBOX env
        # var written in _prepare_env. So here we only gate the flag.
        if self.sandbox_mode != "off":
            cmd.append("--sandbox")
        if self.model:
            cmd.extend(["-m", self.model])
        return cmd

    # ─── prepare_gemini_home ──────────────────────────────────────

    def _prepare_gemini_home(self, sandbox_dir: Path, event_log: EventLogger) -> Path:
        """Set up ``<sandbox>/.gemini_home`` as the CLI's config dir.

        Also scrubs any ``.gemini/`` directory that the benchmark sandbox may
        have inherited — upstream behavior silently overrides system prompt +
        env when that dir is present at the project root (see
        ``GEMINI_SYSTEM_MD`` / ``.gemini/system.md`` in the CLI docs).
        """
        leaked = sandbox_dir / ".gemini"
        if leaked.exists():
            shutil.rmtree(leaked)
            event_log.raw(ev="gemini_scrubbed_project_gemini_dir", path=str(leaked))

        home = sandbox_dir / _GEMINI_HOME_DIRNAME
        home.mkdir(parents=True, exist_ok=True)

        settings = {
            "model": {"name": self.model},
            "general": {"defaultApprovalMode": self.approval_mode},
        }
        (home / "settings.json").write_text(
            json.dumps(settings, indent=2), encoding="utf-8"
        )

        api_key, base_url = _resolve_creds()
        event_log.raw(
            ev="gemini_home_prepared",
            path=str(home),
            has_api_key=bool(api_key),
            has_base_url=bool(base_url),
        )
        return home

    # ─── prepare_env ──────────────────────────────────────────────

    def _prepare_env(self, gemini_home: Path) -> dict[str, str]:
        """Build the subprocess env.

        - ``GEMINI_CLI_HOME`` → the per-sandbox home dir.
        - ``GEMINI_API_KEY`` + ``GOOGLE_GEMINI_BASE_URL`` → resolved from the
          LiteLLM-first credential chain (see module docstring).
        - Scrub ``CLAUDE_CODE_*`` vars so a nested gemini run in a Claude Code
          session doesn't get confused (matches codex's pattern).
        """
        env = os.environ.copy()
        env["GEMINI_CLI_HOME"] = str(gemini_home)
        api_key, base_url = _resolve_creds()
        if api_key:
            env["GEMINI_API_KEY"] = api_key
        if base_url:
            env["GOOGLE_GEMINI_BASE_URL"] = base_url
        # Backend selection for the sandbox flag lives in the env var, not
        # on the CLI. Only set it when sandbox_mode is an explicit backend
        # name — "off" omits both the flag and the env.
        if self.sandbox_mode not in ("off", ""):
            env["GEMINI_SANDBOX"] = self.sandbox_mode
        for k in ("CLAUDECODE", "CLAUDE_CODE_ENTRYPOINT", "CLAUDE_CODE_SSE_PORT"):
            env.pop(k, None)
        return env

    # ─── event routing ────────────────────────────────────────────

    def _route_event(self, event: dict, event_log: EventLogger, state: dict) -> None:
        """Translate a gemini JSONL event into our canonical event stream."""
        etype = event.get("type")
        state["last_event_type"] = etype

        if etype == "init":
            event_log.raw(ev="gemini_init", session_id=event.get("session_id"))
            return
        if etype == "message":
            role = event.get("role")
            content = event.get("content", "")
            if role == "assistant":
                state["turns"] += 1
                event_log.text(content)
            else:
                event_log.raw(ev="gemini_user_message", role=role, content=content)
            return
        if etype == "tool_use":
            event_log.tool_use(
                name=event.get("name", "?"),
                input=event.get("input"),
                id=event.get("id"),
            )
            return
        if etype == "tool_result":
            event_log.tool_result(
                is_error=bool(event.get("is_error")),
                content=event.get("content"),
                tool_use_id=event.get("tool_use_id"),
            )
            return
        if etype == "error":
            state["ok"] = False
            state["last_error"] = f"gemini error: {event.get('message')!r}"
            event_log.error(f"gemini error: {event.get('message')!r}", payload=event)
            return
        if etype == "result":
            usage = (event.get("stats") or {}).get("token_usage")
            if not isinstance(usage, dict):
                usage = event.get("usage") or {}
            if isinstance(usage, dict):
                state["usage"] = {
                    k: v for k, v in usage.items() if isinstance(v, (int, float))
                }
            event_log.raw(ev="gemini_result", payload=event)
            return

        event_log.raw(ev="gemini_unknown", payload=event)

    # ─── require_binary ───────────────────────────────────────────

    def _require_binary(self, event_log: EventLogger) -> None:
        if shutil.which(_GEMINI_BIN) is None:
            event_log.error(
                "gemini binary not on PATH; install from "
                "https://github.com/google-gemini/gemini-cli",
                binary=_GEMINI_BIN,
            )
            raise FileNotFoundError(f"`{_GEMINI_BIN}` not found on PATH")

    # ─── run_inner ────────────────────────────────────────────────

    def _run_inner(
        self,
        *,
        event_log: EventLogger,
        sandbox_dir: Path,
        instruction_file: Path,
    ) -> RunOutcome:
        self._require_binary(event_log)

        gemini_home = self._prepare_gemini_home(sandbox_dir, event_log)
        env = self._prepare_env(gemini_home)
        prompt = instruction_file.read_text(encoding="utf-8")
        cmd = self._build_cmd()

        # Short prompts ride on -p (cleanest); long prompts pipe via stdin
        # (non-TTY stdin + -p is explicitly supported: -p content is appended
        # to stdin per docs).
        prompt_bytes = len(prompt.encode("utf-8"))
        via_stdin = prompt_bytes > _PROMPT_ARG_MAX_BYTES
        if not via_stdin:
            cmd.extend(["-p", prompt])

        event_log.raw(
            ev="gemini_cmd",
            cmd=cmd if not via_stdin else cmd + ["(+stdin prompt)"],
            cwd=str(sandbox_dir),
            gemini_home=str(gemini_home),
            prompt_bytes=prompt_bytes,
            prompt_channel="stdin" if via_stdin else "arg",
        )

        return self._spawn_and_stream(
            cmd=cmd,
            cwd=sandbox_dir,
            env=env,
            prompt=prompt if via_stdin else None,
            event_log=event_log,
        )

    # ─── spawn + stream ───────────────────────────────────────────

    def _spawn_and_stream(
        self,
        *,
        cmd: list[str],
        cwd: Path,
        env: dict[str, str],
        prompt: str | None,
        event_log: EventLogger,
    ) -> RunOutcome:
        stdin_pipe = subprocess.PIPE if prompt is not None else subprocess.DEVNULL
        proc = subprocess.Popen(
            cmd,
            cwd=str(cwd),
            env=env,
            stdin=stdin_pipe,
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
            "turns": 0,
            "ok": True,
            "usage": {},
            "last_error": None,
            "last_event_type": None,
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
                    event_log.raw(ev="stderr", line=stripped)
                except ValueError:
                    # Gemini emits cleanup lines on stderr after stdout EOF;
                    # if our 2-second join(...) timed out the parent may have
                    # already closed the log file. Drop the line rather than
                    # crash the thread.
                    break

        stderr_thread = threading.Thread(target=_drain_stderr, daemon=True)
        stderr_thread.start()

        if prompt is not None:
            try:
                assert proc.stdin is not None
                proc.stdin.write(prompt)
                proc.stdin.close()
            except (BrokenPipeError, OSError) as e:
                event_log.error(f"could not write prompt to gemini stdin: {e}")
                proc.kill()
                timer.cancel()
                return RunOutcome(ok=False, error=f"stdin write failed: {e}")

        assert proc.stdout is not None
        for raw_line in proc.stdout:
            line = raw_line.rstrip("\n")
            if not line:
                continue
            try:
                event = json.loads(line)
            except json.JSONDecodeError:
                event_log.raw(ev="stdout_noise", line=line)
                continue
            self._route_event(event, event_log, state)

        exit_code = proc.wait()
        timer.cancel()
        stderr_thread.join(timeout=2)

        if killed["by_timeout"]:
            state["ok"] = False
            state["last_error"] = (
                f"gemini exceeded {self.timeout_seconds}s and was terminated"
            )

        if exit_code != 0 and state["ok"]:
            # Document exit-code semantics inline — 42 = input error, 53 =
            # turn-limit exceeded per the upstream headless.md.
            if exit_code == 42:
                msg = "gemini input error (exit 42)"
            elif exit_code == 53:
                msg = "gemini turn limit exceeded (exit 53)"
            else:
                msg = (
                    f"gemini exit={exit_code}; last_event={state['last_event_type']!r}"
                )
            state["ok"] = False
            state["last_error"] = msg

        event_log.raw(
            ev="gemini_exit",
            exit_code=exit_code,
            killed_by_timeout=killed["by_timeout"],
            num_turns=state["turns"],
            usage=state["usage"],
        )

        stderr_tail = "".join(stderr_chunks)[-2000:] if stderr_chunks else None

        return RunOutcome(
            ok=state["ok"],
            num_turns=state["turns"],
            total_cost_usd=None,  # gemini does not emit dollars
            usage=state["usage"],
            stderr_tail=stderr_tail,
            error=state["last_error"] if not state["ok"] else None,
            extra={"exit_code": exit_code},
        )
