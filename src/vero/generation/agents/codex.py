"""Codex CLI agent — drives ``codex exec --json`` scoped to a sandbox.

Built on :class:`BaseAgent` so it shares the persistent logging + error handling + timeout plumbing with :class:`ClaudeAgent`.

Codex reference (from the v0.118.0 source we reviewed):

- ``codex exec --json`` emits one JSON envelope per stdout line with ``{"type": <event>, ...}``. All errors + tracing go to stderr (stderr is captured for our ``stderr_tail``).
- Per-turn events ``turn.started`` / ``turn.completed`` / ``turn.failed``. ``turn.completed.usage`` = ``{input_tokens, cached_input_tokens, output_tokens}`` (cumulative). No dollar cost.
- Per-item events ``item.started`` / ``item.updated`` / ``item.completed`` with ``item.type`` ∈ ``{agent_message, reasoning, command_execution, file_change, mcp_tool_call, web_search, todo_list, error, collab_tool_call}``. We route ``agent_message`` to ``event_log.text``, ``reasoning`` to ``event_log.thinking``, all tool kinds (``command_execution`` etc.) to ``event_log.tool_use`` on start and ``event_log.tool_result`` on completion.
- There is no explicit ``run.completed``; the stream simply ends with a terminal ``turn.completed`` / ``turn.failed`` / ``error``.
- No per-run timeout flag — we enforce one via ``subprocess.Popen`` + ``threading.Timer``.

Auth: codex exec honors the ``CODEX_API_KEY`` env var directly — if set, it bypasses any on-disk ``auth.json``. We also write a scoped ``$CODEX_HOME/auth.json`` + ``$CODEX_HOME/config.toml`` under the sandbox so:

1. The user's default ``~/.codex/`` state is never touched.
2. A custom OpenAI base URL (proxied LiteLLM, Azure, etc.) can be passed and is written into ``config.toml`` as a ``model_provider`` override (codex exec does not read ``OPENAI_BASE_URL`` from env).

Credential resolution uses a fallback chain so ``.env`` (already loaded by the CLI) just works without caller-side exports:

- ``api_key``: ``CODEX_AGENT_API_KEY`` → ``LLM_API_KEY`` → ``OPENAI_API_KEY``
- ``base_url``: ``CODEX_AGENT_BASE_URL`` → ``LLM_API_BASE``

``CODEX_AGENT_*`` remains an explicit override when codex needs different creds than the rest of the pipeline. The resolved key is also injected as ``OPENAI_API_KEY`` into the codex subprocess env so the custom-provider ``env_key`` lookup succeeds (the project ``.env`` may leave ``OPENAI_API_KEY`` blank when LiteLLM is the source of truth).
"""

from __future__ import annotations

import json
import os
import select
import shutil
import subprocess
import threading
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

from loguru import logger

from vero.generation.agents.base import BaseAgent, RunOutcome
from vero.generation.agents.event_log import EventLogger
from vero.generation.pricing import UnknownModelError, cost_from_usage

_CODEX_BIN = "codex"

# Per-run CODEX_HOME under the sandbox so we never pollute the user's state.
_CODEX_HOME_DIRNAME = ".codex_home"
_CODEX_LOCAL_HOME_DIRNAME = ".codex_local_home"


def _resolve_creds() -> tuple[str | None, str | None]:
    """Resolve the codex API key + base URL from the environment.

    Fallback chain (first non-empty wins):

    - ``api_key``: ``CODEX_AGENT_API_KEY`` → ``LLM_API_KEY`` → ``OPENAI_API_KEY``
    - ``base_url``: ``CODEX_AGENT_BASE_URL`` → ``LLM_API_BASE``

    Empty strings are treated as unset.
    """
    api_key = (
        os.getenv("CODEX_AGENT_API_KEY")
        or os.getenv("LLM_API_KEY")
        or os.getenv("OPENAI_API_KEY")
        or None
    )
    base_url = os.getenv("CODEX_AGENT_BASE_URL") or os.getenv("LLM_API_BASE") or None
    return api_key, base_url


def _local_codex_home_from_env(env: dict[str, str]) -> Path | None:
    configured = env.get("CODEX_HOME")
    if configured:
        return Path(configured).expanduser()
    home = env.get("HOME")
    if not home:
        return None
    return Path(home).expanduser() / ".codex"


@dataclass
class CodexAgent(BaseAgent):
    """Headless codex-cli runner."""

    model: str | None = None  # passed via -m if set; else codex default
    sandbox_mode: str = (
        "workspace-write"  # "workspace-write" | "read-only" | "danger-full-access"
    )
    skip_git_repo_check: bool = True
    timeout_seconds: int = 1800
    name: str = "codex"
    # Codex enforces the wall-clock cap itself (subprocess watchdog Timer in
    # _spawn_and_stream): on timeout it terminates the subprocess, then still
    # packages state['usage'] into the RunOutcome. So BaseAgent must not layer
    # SIGALRM on top (that would abort before usage is captured).
    self_managed_timeout: bool = True
    # Whether to propagate network access in workspace-write mode; codex
    # default is False, we keep that so the agent can't curl.
    network_access: bool = False
    # Extra `-c key=value` overrides, one per entry.
    config_overrides: list[str] = field(default_factory=list)
    # Accepted for Hydra-config compatibility with ClaudeAgent; codex
    # exec has no streaming-cost hook so we can't honour it. Logged as
    # a warning at run start when set; the cap is enforced by the
    # iterate harness at iteration boundaries instead.
    strict_budget_usd: float | None = None
    # Optional `AgentEnvShim` attached by `cli_dispatch._attach_env_shim`.
    env_shim: Any = None
    # ── Session continuity across time-chunks (in place) ───────────
    # When True, invoke ``codex exec resume --last`` instead of a fresh
    # ``codex exec`` — the agent continues its PRIOR REASONING, not just the
    # on-disk files. The chunked iterate loop sets this for chunks after the
    # first WITHIN an iteration, which reuse the same sandbox dir + the same
    # per-sandbox CODEX_HOME + the same cwd, so ``--last`` (cwd-filtered by
    # default) resolves to the immediately-prior chunk's session. No shared
    # home needed — the sandbox is not rebuilt between chunks of an iteration.
    resume_session: bool = False

    def __post_init__(self) -> None:
        if self.strict_budget_usd is not None:
            logger.warning(
                "codex: strict_budget_usd={} ignored (mid-run cancellation "
                "not supported by `codex exec`); use iterate.budget_usd for "
                "between-iteration caps",
                self.strict_budget_usd,
            )

    def _effective_model(self) -> str | None:
        """The model that will actually serve the run.

        ``self.model`` (the ``-m`` flag) takes precedence, but the eval
        rotation usually pins the model through ``config_overrides`` (e.g.
        ``model=openai.gpt-5.5``) rather than ``agent.model``. When
        ``self.model`` is unset, recover the id from the ``model=…``
        override so cost accounting still finds a pricing entry.
        """
        if self.model:
            return self.model
        for ov in self.config_overrides:
            key, sep, val = ov.partition("=")
            if sep and key.strip() == "model":
                return val.strip().strip("'\"")
        return None

    def _run_start_payload(self) -> dict[str, Any]:
        return {
            "agent": self.name,
            "model": self.model,
            "sandbox_mode": self.sandbox_mode,
            "timeout_seconds": self.timeout_seconds,
            "network_access": self.network_access,
            "strict_budget_usd": self.strict_budget_usd,
        }

    # ─── inner run ─────────────────────────────────────────────

    def _run_inner(
        self,
        *,
        event_log: EventLogger,
        sandbox_dir: Path,
        instruction_file: Path,
    ) -> RunOutcome:
        self._require_binary(event_log)

        env = self._prepare_env(sandbox_dir, event_log)
        codex_home = env.get("CODEX_HOME")
        cmd = self._build_cmd()
        prompt = instruction_file.read_text(encoding="utf-8")

        event_log.raw(
            ev="codex_cmd",
            cmd=cmd,
            cwd=str(sandbox_dir),
            codex_home=str(codex_home) if codex_home else None,
            stdin_bytes=len(prompt.encode("utf-8")),
        )

        return self._spawn_and_stream(
            cmd=cmd,
            cwd=sandbox_dir,
            env=env,
            prompt=prompt,
            event_log=event_log,
        )

    # ─── helpers ───────────────────────────────────────────────

    def _require_binary(self, event_log: EventLogger) -> None:
        if shutil.which(_CODEX_BIN) is None:
            event_log.error(
                "codex binary not on PATH; install from "
                "https://github.com/openai/codex",
                binary=_CODEX_BIN,
            )
            raise FileNotFoundError(f"`{_CODEX_BIN}` not found on PATH")

    def _prepare_codex_home(self, sandbox_dir: Path, event_log: EventLogger) -> Path:
        return self._prepare_codex_home_at(sandbox_dir / _CODEX_HOME_DIRNAME, event_log)

    def _prepare_codex_home_at(self, home: Path, event_log: EventLogger) -> Path:
        home.mkdir(parents=True, exist_ok=True)

        api_key, base_url = _resolve_creds()

        # auth.json — only write if we resolved a key. If the caller uses an
        # existing login, they should set CODEX_HOME via env or rely on
        # CODEX_API_KEY (codex exec picks that up first).
        if api_key:
            (home / "auth.json").write_text(
                json.dumps({"OPENAI_API_KEY": api_key}, indent=2),
                encoding="utf-8",
            )

        # config.toml — write custom base URL / provider if set.
        config_parts: list[str] = ['web_search = "disabled"']
        if base_url:
            config_parts.extend(
                [
                    f'openai_base_url = "{base_url}"',
                    'model_provider = "openai_http"',
                    "",
                    "[model_providers.openai_http]",
                    'name = "OpenAI HTTP"',
                    f'base_url = "{base_url}"',
                    # Tell codex to read the API key from OPENAI_API_KEY env var
                    # (in addition to auth.json). Custom providers default to no
                    # env-var auth, which leads to 401 even when auth.json is
                    # populated; setting ``env_key`` here matches the built-in
                    # ``openai`` provider's behavior.
                    'env_key = "OPENAI_API_KEY"',
                    "supports_websockets = false",
                ]
            )
        (home / "config.toml").write_text(
            "\n".join(config_parts) + "\n", encoding="utf-8"
        )

        event_log.raw(
            ev="codex_home_prepared",
            path=str(home),
            has_api_key=bool(api_key),
            has_base_url=bool(base_url),
        )
        return home

    def _copy_local_codex_home(
        self, sandbox_dir: Path, source_home: Path | None, event_log: EventLogger
    ) -> Path | None:
        """Copy reusable local-login files into a writable per-run CODEX_HOME.

        Nested Codex runs can inherit a readable but non-writable global
        ``CODEX_HOME`` from the outer Codex sandbox. The CLI then fails before
        the first turn when it tries to create app-server/runtime state. Copying
        only stable auth/config files keeps local subscription auth while giving
        the nested process a writable runtime directory.
        """
        if source_home is None or not source_home.exists():
            return None

        home = sandbox_dir / _CODEX_LOCAL_HOME_DIRNAME
        home.mkdir(parents=True, exist_ok=True)
        copied = False
        for rel in ("auth.json", "config.toml", "version.json", "models_cache.json"):
            src = source_home / rel
            if src.is_file():
                shutil.copy2(src, home / rel)
                copied = True
        rules_src = source_home / "rules"
        if rules_src.is_dir():
            shutil.copytree(rules_src, home / "rules", dirs_exist_ok=True)
            copied = True

        if not copied:
            shutil.rmtree(home, ignore_errors=True)
            return None

        event_log.raw(
            ev="codex_home_local_copy",
            source=str(source_home),
            path=str(home),
        )
        return home

    def _prepare_env(self, sandbox_dir: Path, event_log: EventLogger) -> dict[str, str]:
        """Materialize codex's CODEX_HOME and return a process env dict.

        Two paths converge here:

        - When the agent's Hydra config carries a ``config_files`` block
          (the new credentials-profile path), the shim materializes a
          per-sandbox ``.codex/`` dir with a hand-authored ``config.toml``
          (e.g., the OpenRouter provider block). We use that as
          ``CODEX_HOME`` directly and skip the legacy ``_prepare_codex_home``
          single-provider scaffolder.
        - Otherwise (today's litellm default + tests that build CodexAgent
          by hand), fall back to ``_prepare_codex_home`` which emits a
          ``.codex_home/`` dir from ``LLM_API_KEY`` / ``LLM_API_BASE``.
        """
        shim = getattr(self, "env_shim", None)
        shim_config_dir: Path | None = None
        if shim is not None:
            shim.materialize()
            shim_config_dir = shim.materialize_config_dir()
            env = shim.build_env()
        else:
            env = os.environ.copy()
            api_key, _ = _resolve_creds()
            if api_key:
                # ``CODEX_API_KEY`` short-circuits on-disk auth.json in codex
                # exec; ``OPENAI_API_KEY`` is the ``env_key`` our config.toml
                # points at for the custom LiteLLM provider (the repo's .env
                # may leave it blank when LLM_API_KEY is the source of truth).
                env["CODEX_API_KEY"] = api_key
                env["OPENAI_API_KEY"] = api_key

        if shim_config_dir is not None:
            env["CODEX_HOME"] = str(shim_config_dir)
        elif shim is None:
            codex_home = self._prepare_codex_home(sandbox_dir, event_log)
            env["CODEX_HOME"] = str(codex_home)
        else:
            local_home = self._copy_local_codex_home(
                sandbox_dir, _local_codex_home_from_env(env), event_log
            )
            if local_home is not None:
                env["CODEX_HOME"] = str(local_home)
            else:
                event_log.raw(
                    ev="codex_home_global",
                    path=env.get("CODEX_HOME"),
                    reason="no per-agent config_files declared",
                )
        # Scrub claude-code vars so a nested codex run in a Claude Code
        # session doesn't get confused.
        for k in ("CLAUDECODE", "CLAUDE_CODE_ENTRYPOINT", "CLAUDE_CODE_SSE_PORT"):
            env.pop(k, None)
        return env

    def _build_cmd(self) -> list[str]:
        # Two forms:
        #   fresh   : codex exec [--full-auto ...] -
        #   resume  : codex exec resume --last [...] -
        # The resume subcommand continues the most recent session for this cwd
        # — carrying the agent's prior reasoning. Chunks after the first run in
        # the SAME sandbox dir (same cwd, same per-sandbox CODEX_HOME), so the
        # cwd-filtered ``--last`` resolves to the prior chunk's session. It has
        # no ``--full-auto`` flag, so workspace-write is set via ``-c``.
        resuming = self.resume_session
        cmd = [_CODEX_BIN, "exec"]
        if resuming:
            # `resume --last` continues the most recent session for this cwd.
            cmd += ["resume", "--last"]
        cmd.append("--json")
        if self.skip_git_repo_check:
            cmd.append("--skip-git-repo-check")
        # Sandbox flags are identical for the fresh and resume subcommands
        # (`codex exec resume` accepts --full-auto / --sandbox too).
        if self.sandbox_mode == "workspace-write":
            cmd.append("--full-auto")
            if self.network_access:
                cmd.extend(["-c", "sandbox_workspace_write.network_access=true"])
        elif self.sandbox_mode == "read-only":
            cmd.extend(["--sandbox", "read-only"])
        elif self.sandbox_mode == "danger-full-access":
            cmd.append("--dangerously-bypass-approvals-and-sandbox")
        else:
            raise ValueError(f"unknown sandbox_mode {self.sandbox_mode!r}")
        if self.model:
            cmd.extend(["-m", self.model])
        for override in self.config_overrides:
            cmd.extend(["-c", override])
        # ``-`` reads the prompt from stdin (avoids ARG_MAX).
        cmd.append("-")
        return cmd

    # ─── spawn + stream ────────────────────────────────────────

    def _spawn_and_stream(
        self,
        *,
        cmd: list[str],
        cwd: Path,
        env: dict[str, str],
        prompt: str,
        event_log: EventLogger,
    ) -> RunOutcome:
        proc = subprocess.Popen(
            cmd,
            cwd=str(cwd),
            env=env,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            bufsize=1,
        )

        # Watchdog timer — if codex hangs past timeout, terminate.
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

        state = {
            "turns": 0,
            "ok": True,
            "usage": {},
            "last_error": None,
            "last_event_type": None,
        }

        stderr_chunks: list[str] = []

        # Drain stderr on a background thread so a verbose stderr can't
        # wedge codex's own write buffer.
        def _drain_stderr() -> None:
            assert proc.stderr is not None
            for line in proc.stderr:
                stderr_chunks.append(line)
                # Log each non-blank stderr line so we can tail -f the log
                # in real time. JSONL gets the full line verbatim.
                stripped = line.rstrip("\n")
                if not stripped:
                    continue
                try:
                    event_log.raw(ev="stderr", line=stripped)
                except ValueError:
                    # Parent may have closed the log file if join(timeout=2)
                    # timed out — drop the line rather than crash the thread.
                    break

        stderr_thread = threading.Thread(target=_drain_stderr, daemon=True)
        stderr_thread.start()

        # Feed the prompt and close stdin so codex stops waiting.
        try:
            assert proc.stdin is not None
            proc.stdin.write(prompt)
            proc.stdin.close()
        except (BrokenPipeError, OSError) as e:
            event_log.error(f"could not write prompt to codex stdin: {e}")
            proc.kill()
            timer.cancel()
            return RunOutcome(ok=False, error=f"stdin write failed: {e}")

        # Stream stdout line-by-line.
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
                f"codex exec exceeded {self.timeout_seconds}s and was terminated"
            )

        if exit_code != 0 and state["ok"]:
            state["ok"] = False
            state["last_error"] = (
                f"codex exec exit={exit_code}; last_event={state['last_event_type']!r}"
            )

        # Usage fallback: codex only emits ``turn.completed.usage`` when a turn
        # finishes. A run KILLED mid-turn (the 30-min wall-clock cap firing
        # before the agent declares done) leaves ``state['usage']`` empty even
        # though real tokens were spent. Recover the cumulative figure from the
        # rollout JSONL's last ``token_count`` event, which codex updates live
        # throughout the turn. This is what makes per-trial token stats robust
        # under a wall-clock cap.
        if not state["usage"]:
            recovered = self._usage_from_rollout(env.get("CODEX_HOME"))
            if recovered:
                state["usage"] = recovered
                event_log.raw(ev="codex_usage_recovered", usage=recovered)

        event_log.raw(
            ev="codex_exit",
            exit_code=exit_code,
            killed_by_timeout=killed["by_timeout"],
            num_turns=state["turns"],
            usage=state["usage"],
        )

        return self._build_outcome(
            state,
            exit_code=exit_code,
            killed_by_timeout=killed["by_timeout"],
            stderr_chunks=stderr_chunks,
        )

    @staticmethod
    def _usage_from_rollout(codex_home: str | None) -> dict[str, int] | None:
        """Recover cumulative token usage from codex's rollout JSONL.

        codex ≥0.140 writes ``$CODEX_HOME/sessions/**/rollout-*.jsonl`` with
        periodic ``token_count`` events carrying
        ``payload.info.total_token_usage`` = ``{input_tokens,
        cached_input_tokens, output_tokens, reasoning_output_tokens,
        total_tokens}`` — updated live, so the LAST one before a mid-turn kill
        holds the real cumulative spend. Returns that dict (filtered to
        int/float values, matching the ``turn.completed`` shape ``pricing``
        expects), or ``None`` if no rollout / no ``token_count`` is found.
        """
        if not codex_home:
            return None
        sessions = Path(codex_home) / "sessions"
        if not sessions.is_dir():
            return None
        rollouts = sorted(
            sessions.rglob("rollout-*.jsonl"), key=lambda p: p.stat().st_mtime
        )
        if not rollouts:
            return None
        latest = rollouts[-1]
        best: dict[str, int] | None = None
        try:
            with latest.open(encoding="utf-8") as fh:
                for line in fh:
                    line = line.strip()
                    if not line or "token_count" not in line:
                        continue
                    try:
                        ev = json.loads(line)
                    except json.JSONDecodeError:
                        continue
                    payload = ev.get("payload") or {}
                    if payload.get("type") != "token_count":
                        continue
                    info = payload.get("info") or {}
                    total = info.get("total_token_usage")
                    if isinstance(total, dict):
                        best = {
                            k: v
                            for k, v in total.items()
                            if isinstance(v, (int, float))
                        }
        except OSError:
            return None
        return best or None

    def _build_outcome(
        self,
        state: dict,
        *,
        exit_code: int,
        killed_by_timeout: bool,
        stderr_chunks: list[str],
    ) -> RunOutcome:
        """Package final state into a RunOutcome, including a token-derived
        ``total_cost_usd`` when the model is in the pricing table.

        codex exec doesn't emit dollar costs of its own — we compute one
        from ``state['usage']`` (which holds the cumulative figures from
        the final ``turn.completed`` event). Unknown models leave cost
        ``None`` so a missing pricing entry is detectable post-hoc.
        """
        usage = state.get("usage") or {}
        computed_cost: float | None = None
        eff_model = self._effective_model()
        if eff_model:
            try:
                computed_cost = cost_from_usage(eff_model, usage)
            except UnknownModelError:
                logger.warning(
                    "codex: no pricing entry for model {!r}; total_cost_usd left None",
                    eff_model,
                )

        stderr_tail = "".join(stderr_chunks)[-2000:] if stderr_chunks else None

        return RunOutcome(
            ok=state["ok"],
            num_turns=state["turns"],
            total_cost_usd=computed_cost,
            usage=usage,
            stderr_tail=stderr_tail,
            error=state["last_error"] if not state["ok"] else None,
            extra={
                "exit_code": exit_code,
                "computed_cost_usd": computed_cost,
                # True ⇒ the run hit its wall-clock cap (was still working);
                # False ⇒ codex exited on its own (agent declared done / gave
                # up). The chunked iterate loop uses this to tell a checkpoint
                # boundary (resume silently) from a give-up (end the iteration).
                "killed_by_timeout": killed_by_timeout,
            },
        )

    # ─── event routing ────────────────────────────────────────

    def _route_event(self, event: dict, event_log: EventLogger, state: dict) -> None:
        """Translate a codex JSONL event into our canonical event stream."""
        etype = event.get("type")
        state["last_event_type"] = etype

        if etype == "thread.started":
            event_log.raw(ev="codex_thread_started", thread_id=event.get("thread_id"))
            return
        if etype == "turn.started":
            state["turns"] += 1
            event_log.raw(ev="codex_turn_started", turn=state["turns"])
            return
        if etype == "turn.completed":
            usage = event.get("usage") or {}
            if isinstance(usage, dict):
                state["usage"] = {
                    k: v for k, v in usage.items() if isinstance(v, (int, float))
                }
            event_log.raw(
                ev="codex_turn_completed",
                turn=state["turns"],
                usage=usage,
            )
            return
        if etype == "turn.failed":
            state["ok"] = False
            err = event.get("error") or {}
            state["last_error"] = f"codex turn.failed: {err.get('message')!r}"
            event_log.error(
                f"codex turn.failed: {err.get('message')!r}",
                turn=state["turns"],
                error=err,
            )
            return
        if etype == "error":
            state["ok"] = False
            state["last_error"] = f"codex error: {event.get('message')!r}"
            event_log.error(
                f"codex error: {event.get('message')!r}",
                payload=event,
            )
            return

        if etype in {"item.started", "item.updated", "item.completed"}:
            self._route_item(etype, event.get("item") or {}, event_log)
            return

        event_log.raw(ev="codex_unknown", payload=event)

    def _route_item(self, phase: str, item: dict, event_log: EventLogger) -> None:
        itype = item.get("type") or item.get("kind") or "?"
        item_id = item.get("id")

        if itype == "agent_message":
            text = item.get("text", "")
            # Emit on completed (final assistant message); start/update
            # tend to be partials we don't need to double-log.
            if phase == "item.completed":
                event_log.text(text)
            else:
                event_log.raw(ev="codex_item", phase=phase, type=itype, text=text)
            return

        if itype == "reasoning":
            text = item.get("text") or item.get("content", "")
            if phase == "item.completed":
                event_log.thinking(text)
            else:
                event_log.raw(ev="codex_item", phase=phase, type=itype, text=text)
            return

        if itype == "command_execution":
            command = item.get("command")
            status = item.get("status")
            aggregated = item.get("aggregated_output")
            exit_code = item.get("exit_code")
            if phase == "item.started":
                event_log.tool_use(
                    name="bash",
                    input={"command": command},
                    id=item_id,
                )
            elif phase == "item.completed":
                event_log.tool_result(
                    is_error=(status in {"failed", "declined"})
                    or (exit_code not in (None, 0)),
                    content={
                        "status": status,
                        "exit_code": exit_code,
                        "aggregated_output": aggregated,
                    },
                    tool_use_id=item_id,
                )
            else:
                event_log.raw(
                    ev="codex_item",
                    phase=phase,
                    type=itype,
                    command=command,
                    status=status,
                )
            return

        if itype == "file_change":
            changes = item.get("changes") or []
            status = item.get("status")
            if phase == "item.started":
                event_log.tool_use(
                    name="file_change",
                    input={"changes": changes},
                    id=item_id,
                )
            elif phase == "item.completed":
                event_log.tool_result(
                    is_error=(status in {"failed", "declined"}),
                    content={"status": status, "changes": changes},
                    tool_use_id=item_id,
                )
            return

        if itype == "mcp_tool_call":
            if phase == "item.started":
                event_log.tool_use(
                    name=f"mcp:{item.get('server')}/{item.get('tool')}",
                    input=item.get("arguments"),
                    id=item_id,
                )
            elif phase == "item.completed":
                event_log.tool_result(
                    is_error=item.get("status") == "failed" or bool(item.get("error")),
                    content={
                        "status": item.get("status"),
                        "result": item.get("result"),
                        "error": item.get("error"),
                    },
                    tool_use_id=item_id,
                )
            return

        # Anything else — web_search, todo_list, collab_tool_call, etc.
        event_log.raw(ev="codex_item", phase=phase, type=itype, item=item)


# ``select`` import kept even if unused elsewhere — some platforms where
# we later drop a non-blocking stdout read will need it.
_ = select
