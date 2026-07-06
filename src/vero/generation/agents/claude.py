"""Claude Code agent — drives ``claude_agent_sdk.query`` scoped to a sandbox.

Now built on top of :class:`vero.generation.agents.base.BaseAgent`, so
every event is persisted to the sandbox's ``agent_events.jsonl`` +
``agent.log`` and ``ResultMessage.total_cost_usd`` / ``num_turns`` land
in the shared :class:`AgentResult` shape.
"""

from __future__ import annotations

import os
import time
from dataclasses import dataclass, replace
from pathlib import Path
from typing import Any

import anyio
from claude_agent_sdk import (
    AssistantMessage,
    ClaudeAgentOptions,
    ResultMessage,
    TextBlock,
    ThinkingBlock,
    ToolResultBlock,
    ToolUseBlock,
    query,
)
from loguru import logger

from vero.generation.agents.base import BaseAgent, RunOutcome
from vero.generation.agents.event_log import EventLogger
from vero.generation.pricing import UnknownModelError, cost_from_usage

_SYSTEM_PROMPT = """\
You are an expert Lean 4 engineer working in a local benchmark sandbox.
The sandbox is the current working directory. The task is defined in
``INSTRUCTION.md`` at the sandbox root — READ IT FIRST.

Hard rules:
- Only edit the *interior* of ``-- !benchmark @start …`` / ``-- !benchmark @end …``
  marker pairs. Never modify the marker lines themselves.
- Do not introduce ``axiom`` declarations.
- Do not touch frozen files (Harness/Bundle/Test/Spec/lakefile.toml/…).
- Run ``lake build`` as your oracle; iterate until it succeeds AND the
  filled proofs do not rely on ``sorry``.
- Prefer tight, idiomatic Lean 4 proofs. ``simp``, ``omega``, ``decide``,
  ``rfl``, ``exact``, ``intro``/``constructor`` are your friends.

When you are done (or you give up), emit a concise status summary.
"""

# Sentinel the model emits to signal a terminal stop (finished OR giving up).
# The resume loop keeps resuming the session until it sees this (or the wall).
_STOP_TOKEN = "<<<VERO_STOP>>>"


@dataclass
class ClaudeAgent(BaseAgent):
    """Headless Claude Code runner.

    When ``timeout_seconds > 0`` the agent runs a **self-managed resume loop**
    (like CodexAgent runs its own exec loop to the wall): a single
    ``query()`` returns at the first ``end_turn``, well before a 90-min
    budget, so we keep **resuming the same session** — context preserved —
    round after round until one of: the model signals DONE, the model gives
    up, or the wall-clock cap fires. Give-up is a clean stop; escalation is
    the outer iterate harness's job. On the wall we set
    ``extra['killed_by_timeout']=True`` so the sampled runner treats it as
    terminal (not a transient failure to retry). ``timeout_seconds == 0``
    keeps the legacy single-``query()`` path.
    """

    model: str = "claude-sonnet-4-5"
    max_turns: int = 40
    name: str = "claude"
    # Adaptive reasoning effort for opus-4.7+ (drives output_config.effort:
    # low|medium|high|xhigh|max). Higher = more thinking. Ignored for non-opus.
    effort: str = "medium"
    timeout_seconds: int = (
        0  # 0 = single query(); >0 = self-managed resume loop to wall
    )
    # ClaudeAgent enforces its own wall-clock cap inside the resume loop
    # (anyio.move_on_after per round + a cumulative deadline), returning a
    # full RunOutcome with usage/cost on timeout. So BaseAgent must NOT wrap
    # us in a SIGALRM timer — that would abort mid-round and drop token stats.
    self_managed_timeout: bool = True
    # Mid-run $ cap (SDK-only feature). When set, the async iterator
    # breaks as soon as cumulative ResultMessage.total_cost_usd crosses
    # this value, and RunOutcome.extra['over_strict_budget']=True. None
    # disables the cap. Distinct from iterate.budget_usd, which is a
    # post-hoc cap applied between iterations.
    strict_budget_usd: float | None = None
    # Optional AgentEnvShim from the Hydra config. Populated by create_agent.
    env_shim: Any = None

    def _run_start_payload(self) -> dict[str, Any]:
        return {
            "agent": self.name,
            "model": self.model,
            "max_turns": self.max_turns,
            "effort": self.effort,
            "timeout_seconds": self.timeout_seconds,
            "strict_budget_usd": self.strict_budget_usd,
        }

    def _run_inner(
        self,
        *,
        event_log: EventLogger,
        sandbox_dir: Path,
        instruction_file: Path,
    ) -> RunOutcome:
        prompt = (
            "The sandbox is the current working directory. Please read "
            "INSTRUCTION.md at the sandbox root and execute the task "
            "end-to-end. Run `lake build` frequently to check your work. "
            "This is a long-horizon task: keep working until every marker is "
            "filled and the build is clean with no `sorry`. Do NOT stop early "
            "to ask questions or to report partial progress — you are running "
            "autonomously and no one will answer.\n\n"
            "STOP PROTOCOL: only when you are either (a) completely finished "
            "(build clean, no sorry) OR (b) genuinely stuck and giving up, "
            f"end your final message with a line containing exactly "
            f"{_STOP_TOKEN}. Until you emit that token you will be asked to "
            "continue.\n\n"
            f"Sandbox: {sandbox_dir}\n"
            f"Instruction: {instruction_file}\n"
        )
        # Nudge used to resume the SAME session (context preserved) after a
        # round ends at end_turn without the stop token.
        resume_prompt = (
            "Continue the task from where you left off. Run `lake build` to "
            "re-check state, then keep filling markers / fixing proofs. "
            f"Remember the STOP PROTOCOL: emit {_STOP_TOKEN} on its own line "
            "ONLY when the build is fully clean with no `sorry`, or when you "
            "are giving up. Otherwise just keep working."
        )

        # Credential plumbing: when an `AgentEnvShim` is attached, let it scope
        # ANTHROPIC_API_KEY / ANTHROPIC_BASE_URL for just this run and restore
        # whatever os.environ held before on exit. When not (e.g., in legacy
        # tests that build ClaudeAgent directly), preserve the old setdefault
        # behaviour so existing smoke paths keep working.
        shim = getattr(self, "env_shim", None)
        if shim is not None:
            shim.materialize()
            # Per-sandbox CLI config dir (e.g., settings.json with the
            # right ANTHROPIC_BASE_URL / ANTHROPIC_AUTH_TOKEN for an
            # OpenRouter route). Setting CLAUDE_CONFIG_DIR scopes the
            # bundled CLI to this dir so its settings.json wins over
            # ~/.claude/settings.json — the only sturdy way to override
            # the env block the CLI re-reads after we set os.environ.
            config_dir = shim.materialize_config_dir()
            if config_dir is not None:
                shim.env_declared = {
                    **dict(shim.env_declared),
                    "CLAUDE_CONFIG_DIR": str(config_dir),
                }
        else:
            if k := os.getenv("CLAUDE_AGENT_API_KEY"):
                os.environ.setdefault("ANTHROPIC_API_KEY", k)
            if base := os.getenv("CLAUDE_AGENT_API_BASE"):
                os.environ.setdefault("ANTHROPIC_BASE_URL", base)

        # Opus 4.7+ reasoning is driven by adaptive thinking + --effort. The
        # Claude Agent SDK (>=0.2) maps thinking={type:"adaptive"} -> the native
        # `--thinking adaptive` CLI flag and effort -> `--effort <level>`
        # (subprocess_cli.py). thinking={type:"disabled"} maps to
        # `--thinking disabled`, i.e. reasoning OFF — the earlier disabled
        # setting silenced thinking despite the effort flag. Use adaptive so
        # effort:high actually buys extended reasoning.
        opus_extra = (
            {"thinking": {"type": "adaptive"}, "effort": self.effort}
            if "opus" in (self.model or "").lower()
            else {}
        )

        # When the shim has materialized a scoped CLAUDE_CONFIG_DIR with a
        # settings.json (env block, model aliases, etc.), the SDK must be
        # told to actually load it via setting_sources=["user"]. The
        # default None means "load no settings files" — the env block in
        # our scoped settings.json gets ignored otherwise.
        scoped_config = shim is not None and shim.config_files
        setting_sources = ["user"] if scoped_config else None

        options = ClaudeAgentOptions(
            system_prompt=_SYSTEM_PROMPT,
            max_turns=self.max_turns,
            allowed_tools=[
                "Read",
                "Write",
                "Edit",
                "Glob",
                "Grep",
                "Bash(lake*)",
                "Bash(ls*)",
                "Bash(cat*)",
                "Bash(find*)",
            ],
            permission_mode="acceptEdits",
            cwd=str(sandbox_dir),
            model=self.model,
            setting_sources=setting_sources,
            **opus_extra,
        )

        state = {
            "turns": 0,
            "cost": None,
            "ok": True,
            "last_error": None,
            "usage": {},
            "over_strict_budget": False,
            "killed_by_timeout": False,
            "rounds": 0,
            "stopped": False,  # model emitted the stop token (done OR gave up)
            "session_id": None,
        }
        strict_cap = self.strict_budget_usd
        # Wall-clock deadline for the whole run. 0 ⇒ single query(), no loop.
        deadline = (
            time.monotonic() + self.timeout_seconds
            if self.timeout_seconds and self.timeout_seconds > 0
            else None
        )

        def _consume_message(message: Any) -> None:
            """Log one SDK message and fold its result into ``state``."""
            if isinstance(message, AssistantMessage):
                sid = getattr(message, "session_id", None)
                if sid:
                    state["session_id"] = sid
                for block in message.content:
                    if isinstance(block, ThinkingBlock):
                        event_log.thinking(block.thinking)
                    elif isinstance(block, TextBlock):
                        event_log.text(block.text)
                        if _STOP_TOKEN in (block.text or ""):
                            state["stopped"] = True
                    elif isinstance(block, ToolUseBlock):
                        event_log.tool_use(
                            name=block.name,
                            input=block.input,
                            id=getattr(block, "id", None),
                        )
                    elif isinstance(block, ToolResultBlock):
                        event_log.tool_result(
                            is_error=bool(block.is_error),
                            content=block.content,
                            tool_use_id=getattr(block, "tool_use_id", None),
                        )
            elif isinstance(message, ResultMessage):
                state["turns"] += message.num_turns or 0
                sid = getattr(message, "session_id", None)
                if sid:
                    state["session_id"] = sid
                # Accumulate (not overwrite) — every round + every per-segment
                # ResultMessage contributes; strict cap fires on the total.
                if message.total_cost_usd is not None:
                    state["cost"] = (state["cost"] or 0.0) + message.total_cost_usd
                if message.is_error:
                    state["ok"] = False
                usage = getattr(message, "usage", None)
                if isinstance(usage, dict):
                    # Usage is cumulative per session; keep the latest snapshot.
                    state["usage"] = {
                        k: v for k, v in usage.items() if isinstance(v, (int, float))
                    }
                event_log.raw(
                    ev="result",
                    round=state["rounds"],
                    num_turns=message.num_turns,
                    total_cost_usd=message.total_cost_usd,
                    cumulative_cost_usd=state["cost"],
                    is_error=message.is_error,
                    usage=state["usage"],
                )
                if (
                    strict_cap is not None
                    and state["cost"] is not None
                    and state["cost"] >= strict_cap
                ):
                    state["over_strict_budget"] = True

        async def _drive_round(round_prompt: str, resume_id: str | None) -> None:
            """Run one query() round (fresh or resumed), draining its stream.

            Breaks the async iterator early on a crossed strict budget so the
            outer loop can stop. Uses a per-round move_on_after slice so a
            single hung round can't blow past the wall.
            """
            opts = options
            if resume_id is not None:
                opts = replace(options, resume=resume_id, continue_conversation=False)

            async def _pump() -> None:
                async for message in query(prompt=round_prompt, options=opts):
                    _consume_message(message)
                    if state["over_strict_budget"]:
                        logger.warning(
                            "claude: strict_budget_usd={} crossed (cumulative={:.4f}); cancelling iterator",
                            strict_cap,
                            state["cost"],
                        )
                        event_log.raw(
                            ev="strict_budget_cancel",
                            strict_budget_usd=strict_cap,
                            cumulative_cost_usd=state["cost"],
                        )
                        return

            if deadline is not None:
                remaining = deadline - time.monotonic()
                if remaining <= 0:
                    return
                with anyio.move_on_after(remaining):
                    await _pump()
            else:
                await _pump()

        async def _drive() -> None:
            # Round 0: fresh session. Subsequent rounds resume it (context
            # preserved). Stop on: model stop token, strict budget, wall, or a
            # round that produced no resumable session id.
            round_prompt = prompt
            resume_id: str | None = None
            while True:
                state["rounds"] += 1
                await _drive_round(round_prompt, resume_id)

                if state["stopped"]:
                    event_log.raw(ev="stop_token_seen", round=state["rounds"])
                    return
                if state["over_strict_budget"]:
                    return
                if deadline is None:
                    return  # legacy single-shot: no loop
                if time.monotonic() >= deadline:
                    state["killed_by_timeout"] = True
                    event_log.raw(ev="wall_clock_hit", round=state["rounds"])
                    return
                if not state["session_id"]:
                    # Can't resume without a session id — treat as done.
                    logger.warning(
                        "claude: no session_id to resume; ending after round {}",
                        state["rounds"],
                    )
                    return
                # Resume the SAME session; context is preserved server-side.
                resume_id = state["session_id"]
                round_prompt = resume_prompt
                event_log.raw(
                    ev="resume",
                    round=state["rounds"] + 1,
                    session_id=resume_id,
                    remaining_seconds=round(deadline - time.monotonic(), 1),
                )

        try:
            if shim is not None:
                with shim.scoped_environ():
                    anyio.run(_drive)
            else:
                anyio.run(_drive)
        except Exception as e:  # noqa: BLE001
            state["ok"] = False
            state["last_error"] = f"{type(e).__name__}: {e}"
            event_log.error(
                f"claude_agent_sdk raised: {type(e).__name__}: {e}",
                error_type=type(e).__name__,
            )

        canonical, sdk_cost, token_cost = self._resolve_costs(
            state["cost"], state["usage"]
        )

        # A wall-clock stop is a clean terminal outcome (ok stays True unless a
        # round itself errored): the sampled runner keys "transient vs terminal"
        # off killed_by_timeout, and we ran the full budget as intended.
        return RunOutcome(
            ok=state["ok"],
            num_turns=state["turns"],
            total_cost_usd=canonical,
            usage=state["usage"],
            stderr_tail=state["last_error"],
            error=state["last_error"] if not state["ok"] else None,
            extra={
                "computed_cost_usd": token_cost,
                "sdk_cost_usd": sdk_cost,
                "over_strict_budget": state["over_strict_budget"],
                "killed_by_timeout": state["killed_by_timeout"],
                "rounds": state["rounds"],
                "stopped_by_token": state["stopped"],
            },
        )

    def _resolve_costs(
        self,
        sdk_cost: float | None,
        usage: dict[str, int | float],
    ) -> tuple[float | None, float | None, float | None]:
        """Pick the canonical ``total_cost_usd`` and surface both source figures.

        Returns ``(canonical, sdk, token)``:

        - ``canonical`` is what the iterate harness sees as
          ``total_cost_usd`` and uses for ``iterate.budget_usd`` caps.
          We prefer the SDK-reported number when available because
          Anthropic's billing includes per-call overhead (cache-write
          surcharges, extended-context tiers, subscription metering)
          that our pricing table doesn't fully model. Empirically,
          token-derived costs ran 3–9× under the SDK number on
          bankledger smoke turns.
        - ``token`` is :func:`pricing.cost_from_usage` of ``usage`` —
          kept for cross-check + analysis even though it isn't the
          canonical cost. Stays useful for verifying that the SDK
          number is in the right ballpark and for unit-rate sanity
          checks across model versions.
        - ``sdk`` is the value the SDK reported, passed through.

        Fallbacks: when the SDK doesn't report a cost (shouldn't happen
        for the API path but is here for defence + tests), the token
        figure becomes canonical. Unknown models warn-log and surface
        ``token=None``.
        """
        token_cost: float | None = None
        if usage:
            try:
                token_cost = cost_from_usage(self.model, usage)
            except UnknownModelError:
                logger.warning(
                    "claude: no pricing entry for model {!r}; "
                    "computed_cost_usd will be None (canonical falls back to SDK figure)",
                    self.model,
                )
        canonical = sdk_cost if sdk_cost is not None else token_cost
        return canonical, sdk_cost, token_cost
