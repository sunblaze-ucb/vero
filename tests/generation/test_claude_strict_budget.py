"""Tests for ``ClaudeAgent.strict_budget_usd`` — mid-run cancellation.

The SDK's ``query()`` may emit multiple ResultMessages over a multi-turn
run; we accumulate ``total_cost_usd`` from each and break out of the
async iterator when cumulative cost crosses ``strict_budget_usd``. The
run is then marked ``over_strict_budget`` in ``RunOutcome.extra``.

If the SDK only ever emits one terminal ResultMessage (single-turn
session), strict_budget effectively becomes a post-hoc flag — the run
already finished — but the bookkeeping still surfaces it for analysis.
"""

from __future__ import annotations

from pathlib import Path
from unittest.mock import MagicMock, patch

from claude_agent_sdk import ResultMessage

from vero.generation.agents.claude import ClaudeAgent


def _fake_result_msg(cost: float, *, num_turns: int = 1) -> ResultMessage:
    msg = MagicMock(spec=ResultMessage)
    msg.num_turns = num_turns
    msg.total_cost_usd = cost
    msg.is_error = False
    msg.usage = {"input_tokens": 0, "output_tokens": 0}
    return msg


def test_strict_budget_field_default_none() -> None:
    agent = ClaudeAgent(model="claude-sonnet-4-6")
    assert agent.strict_budget_usd is None


def test_strict_budget_breaks_iterator_when_crossed(tmp_path: Path) -> None:
    """3 ResultMessages × $0.4 → cumulative crosses $1.0 cap on #3.
    Iterator should be drained at most up to the message that crosses."""
    agent = ClaudeAgent(
        model="claude-sonnet-4-6",
        strict_budget_usd=1.0,
        max_turns=10,
    )

    sandbox = tmp_path / "sb"
    sandbox.mkdir()
    instr = sandbox / "INSTRUCTION.md"
    instr.write_text("dummy")

    msgs = [
        _fake_result_msg(0.4),
        _fake_result_msg(0.4),
        _fake_result_msg(0.4),
        _fake_result_msg(0.4),
    ]

    requested = {"n": 0}

    async def fake_query(*, prompt, options):
        for m in msgs:
            requested["n"] += 1
            yield m

    with patch("vero.generation.agents.claude.query", side_effect=fake_query):
        result = agent.run(sandbox_dir=sandbox, instruction_file=instr)

    # Cumulative: $0.4 (#1) → $0.8 (#2) → $1.2 (#3, > cap, break before #4).
    assert requested["n"] == 3
    assert result.extra.get("over_strict_budget") is True


def test_strict_budget_unset_drains_full_stream(tmp_path: Path) -> None:
    """No cap → iterator runs to completion (4 messages all consumed)."""
    agent = ClaudeAgent(model="claude-sonnet-4-6")  # strict_budget_usd default None

    sandbox = tmp_path / "sb"
    sandbox.mkdir()
    instr = sandbox / "INSTRUCTION.md"
    instr.write_text("dummy")

    msgs = [_fake_result_msg(0.4) for _ in range(4)]
    requested = {"n": 0}

    async def fake_query(*, prompt, options):
        for m in msgs:
            requested["n"] += 1
            yield m

    with patch("vero.generation.agents.claude.query", side_effect=fake_query):
        result = agent.run(sandbox_dir=sandbox, instruction_file=instr)

    assert requested["n"] == 4
    assert not result.extra.get("over_strict_budget")


def test_strict_budget_unmet_drains_full_stream(tmp_path: Path) -> None:
    """Cap higher than total cost → no break."""
    agent = ClaudeAgent(model="claude-sonnet-4-6", strict_budget_usd=10.0)

    sandbox = tmp_path / "sb"
    sandbox.mkdir()
    instr = sandbox / "INSTRUCTION.md"
    instr.write_text("dummy")

    msgs = [_fake_result_msg(0.4) for _ in range(3)]
    requested = {"n": 0}

    async def fake_query(*, prompt, options):
        for m in msgs:
            requested["n"] += 1
            yield m

    with patch("vero.generation.agents.claude.query", side_effect=fake_query):
        result = agent.run(sandbox_dir=sandbox, instruction_file=instr)

    assert requested["n"] == 3
    assert not result.extra.get("over_strict_budget")
