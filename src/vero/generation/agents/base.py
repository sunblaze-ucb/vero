"""Agent protocol + BaseAgent — shared infrastructure for every backend.

Every concrete agent subclasses :class:`BaseAgent` and implements ``_run_inner(event_log, sandbox_dir, instruction_file) -> RunOutcome``. The base class handles the universals:

- Validate the instruction file exists.
- Open an :class:`EventLogger` writing ``agent_events.jsonl`` + ``agent.log`` into the sandbox (full-fidelity JSONL, readable mirror).
- Emit ``run_start`` / ``run_end`` events.
- Catch and log any exception as a ``run_error`` event so the log file is always self-describing even when a run crashes.
- Enforce an optional wall-clock timeout via a watchdog thread that raises ``TimeoutError`` into the inner run.
- Package the outcome into an :class:`AgentResult`.

Subclasses never touch the event log directly from outside the ``_run_inner`` contract; every event runs through the logger so the JSONL stream stays canonical.
"""

from __future__ import annotations

import signal
import threading
import time
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Protocol

from loguru import logger

from vero.generation.agents.event_log import EventLogger


@dataclass
class AgentResult:
    """Outcome of one agent run."""

    sandbox_dir: Path
    ok: bool
    num_turns: int = 0
    total_cost_usd: float | None = None
    usage: dict[str, int] = field(default_factory=dict)
    stderr_tail: str | None = None
    error: str | None = None
    elapsed_seconds: float | None = None
    event_log_path: Path | None = None
    text_log_path: Path | None = None
    extra: dict[str, Any] = field(default_factory=dict)


@dataclass
class RunOutcome:
    """Return value from ``BaseAgent._run_inner``."""

    ok: bool = True
    num_turns: int = 0
    total_cost_usd: float | None = None
    usage: dict[str, int] = field(default_factory=dict)
    stderr_tail: str | None = None
    error: str | None = None
    extra: dict[str, Any] = field(default_factory=dict)


class Agent(Protocol):
    """Any object that can drive an LLM to edit a sandbox."""

    name: str

    def run(self, *, sandbox_dir: Path, instruction_file: Path) -> AgentResult: ...


class BaseAgent:
    """Common lifecycle + logging + error handling shared by every backend.

    Subclasses override :meth:`_run_inner`. Must set ``name`` at class level.
    """

    name: str = "base"
    timeout_seconds: int | None = None
    # When True, the agent enforces its own wall-clock timeout internally
    # (e.g. CodexAgent's subprocess watchdog Timer) and returns a normal
    # RunOutcome *with usage/cost populated* when the cap is hit. In that
    # case BaseAgent must NOT wrap the run in a SIGALRM timer: a SIGALRM
    # raised mid-stream aborts the agent before it can package its usage,
    # so token stats are lost on exactly the timeout every capped trial
    # hits. Leave False for agents with no internal timeout (SIGALRM is the
    # only cap available for them).
    self_managed_timeout: bool = False

    def _run_inner(
        self,
        *,
        event_log: EventLogger,
        sandbox_dir: Path,
        instruction_file: Path,
    ) -> RunOutcome:  # pragma: no cover - abstract
        raise NotImplementedError

    def _run_start_payload(self) -> dict[str, Any]:
        """Overridable — agents can publish their config at run_start."""
        return {"agent": self.name, "timeout_seconds": self.timeout_seconds}

    # ─── orchestration ─────────────────────────────────────────

    def run(self, *, sandbox_dir: Path, instruction_file: Path) -> AgentResult:
        sandbox_dir = Path(sandbox_dir).resolve()
        instruction_file = Path(instruction_file).resolve()
        if not instruction_file.is_file():
            raise FileNotFoundError(instruction_file)

        started = time.monotonic()
        with EventLogger(agent=self.name, sandbox_dir=sandbox_dir) as event_log:
            event_log.run_start(**self._run_start_payload())

            outcome: RunOutcome
            try:
                outcome = self._with_timeout(event_log, sandbox_dir, instruction_file)
            except TimeoutError as e:
                # Tag killed_by_timeout so the sampled runner treats a
                # wall-clock cap as TERMINAL, not a transient failure to retry.
                # (dispatch_generation reads this from extra; without it a
                # timed-out cell would be relaunched up to max_transient_retries
                # times, each another full wall — see cli_dispatch/cli_iterate.)
                outcome = RunOutcome(
                    ok=False,
                    error=f"timeout after {self.timeout_seconds}s: {e}",
                    extra={"killed_by_timeout": True},
                )
                event_log.error(
                    "agent exceeded its wall-clock budget",
                    timeout_seconds=self.timeout_seconds,
                )
            except BaseException as e:  # noqa: BLE001
                outcome = RunOutcome(ok=False, error=f"{type(e).__name__}: {e}")
                event_log.error(
                    f"{type(e).__name__}: {e}",
                    error_type=type(e).__name__,
                )
                logger.exception("agent {} run raised", self.name)

            elapsed = time.monotonic() - started
            extra = outcome.extra or {}
            event_log.run_end(
                ok=outcome.ok,
                num_turns=outcome.num_turns,
                total_cost_usd=outcome.total_cost_usd,
                computed_cost_usd=extra.get("computed_cost_usd"),
                sdk_cost_usd=extra.get("sdk_cost_usd"),
                usage=outcome.usage,
                elapsed_seconds=round(elapsed, 3),
                error=outcome.error,
            )
            return AgentResult(
                sandbox_dir=sandbox_dir,
                ok=outcome.ok,
                num_turns=outcome.num_turns,
                total_cost_usd=outcome.total_cost_usd,
                usage=outcome.usage,
                stderr_tail=outcome.stderr_tail,
                error=outcome.error,
                elapsed_seconds=elapsed,
                event_log_path=event_log.jsonl_path,
                text_log_path=event_log.text_path,
                extra=outcome.extra,
            )

    # ─── timeout ──────────────────────────────────────────────

    def _with_timeout(
        self,
        event_log: EventLogger,
        sandbox_dir: Path,
        instruction_file: Path,
    ) -> RunOutcome:
        """Run _run_inner under an optional wall-clock timeout.

        Using a SIGALRM-based timer when available on the main thread;
        falling back to a watchdog thread that sets a shared flag (the
        inner agent cooperates by checking or by being killed by the
        subprocess timeout in its own pipe — see CodexAgent).
        """
        if self.timeout_seconds is None or self.timeout_seconds <= 0:
            return self._run_inner(
                event_log=event_log,
                sandbox_dir=sandbox_dir,
                instruction_file=instruction_file,
            )

        # Agents that manage their own wall-clock cap (codex's watchdog Timer)
        # return a full RunOutcome — usage + cost included — when they hit it.
        # Wrapping them in SIGALRM would abort mid-stream and drop that usage,
        # which is exactly the token stats we need on every capped trial. Let
        # them self-terminate gracefully.
        if self.self_managed_timeout:
            return self._run_inner(
                event_log=event_log,
                sandbox_dir=sandbox_dir,
                instruction_file=instruction_file,
            )

        main_thread = threading.current_thread() is threading.main_thread()
        if main_thread and hasattr(signal, "SIGALRM"):
            return self._with_sigalrm_timeout(event_log, sandbox_dir, instruction_file)
        # Best effort — just run and rely on the subprocess-level timeout.
        return self._run_inner(
            event_log=event_log,
            sandbox_dir=sandbox_dir,
            instruction_file=instruction_file,
        )

    def _with_sigalrm_timeout(
        self,
        event_log: EventLogger,
        sandbox_dir: Path,
        instruction_file: Path,
    ) -> RunOutcome:
        def handler(_signum, _frame):
            raise TimeoutError(f"agent {self.name!r} exceeded {self.timeout_seconds}s")

        prev = signal.signal(signal.SIGALRM, handler)
        signal.alarm(self.timeout_seconds or 0)
        try:
            return self._run_inner(
                event_log=event_log,
                sandbox_dir=sandbox_dir,
                instruction_file=instruction_file,
            )
        finally:
            signal.alarm(0)
            signal.signal(signal.SIGALRM, prev)


# ─── factory ────────────────────────────────────────────────────


def create_agent(
    kind: str,
    *,
    model: str | None = None,
    max_turns: int = 40,
    timeout_seconds: int | None = None,
    **kw: Any,
) -> Agent:
    """Return an :class:`Agent` instance for the named backend."""
    if kind == "claude":
        from vero.generation.agents.claude import ClaudeAgent

        return ClaudeAgent(
            model=model or "claude-sonnet-4-5",
            max_turns=max_turns,
            timeout_seconds=timeout_seconds or 0,
            **kw,
        )
    if kind == "codex":
        from vero.generation.agents.codex import CodexAgent

        return CodexAgent(
            model=model,
            timeout_seconds=timeout_seconds or 1800,
            **kw,
        )
    if kind == "gemini":
        from vero.generation.agents.gemini import GeminiAgent

        return GeminiAgent(
            model=model or "gemini-3.1-pro-preview",
            timeout_seconds=timeout_seconds or 1800,
            **kw,
        )
    if kind == "gauss":
        from vero.generation.agents.gauss import GaussAgent

        return GaussAgent(
            model=model,
            timeout_seconds=timeout_seconds or 1800,
            **kw,
        )
    raise ValueError(f"unknown agent kind {kind!r}")
