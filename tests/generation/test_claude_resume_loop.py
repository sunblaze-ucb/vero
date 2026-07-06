"""Tests for ``ClaudeAgent``'s self-managed resume loop (``timeout_seconds > 0``).

A single ``query()`` returns at the first ``end_turn``, well under a long
wall-clock budget. To match how CodexAgent runs its own exec loop to the
wall, ClaudeAgent (when ``timeout_seconds > 0``) keeps **resuming the same
session** — context preserved via ``resume=<session_id>`` — until one of:
the model emits the stop token (finished OR gave up), the wall fires, or a
round yields no resumable session id. ``timeout_seconds == 0`` keeps the
legacy single-``query()`` path (exercised by test_claude_strict_budget).
"""

from __future__ import annotations

from pathlib import Path
from unittest.mock import MagicMock, patch

from claude_agent_sdk import AssistantMessage, ResultMessage, TextBlock

from vero.generation.agents.claude import _STOP_TOKEN, ClaudeAgent


def _assistant(text: str, session_id: str = "sess-1") -> AssistantMessage:
    msg = MagicMock(spec=AssistantMessage)
    block = MagicMock(spec=TextBlock)
    block.text = text
    msg.content = [block]
    msg.session_id = session_id
    return msg


def _result(
    cost: float, *, num_turns: int = 1, session_id: str = "sess-1"
) -> ResultMessage:
    msg = MagicMock(spec=ResultMessage)
    msg.num_turns = num_turns
    msg.total_cost_usd = cost
    msg.is_error = False
    msg.usage = {"input_tokens": 10, "output_tokens": 5}
    msg.session_id = session_id
    return msg


def _sandbox(tmp_path: Path) -> tuple[Path, Path]:
    sb = tmp_path / "sb"
    sb.mkdir()
    instr = sb / "INSTRUCTION.md"
    instr.write_text("dummy")
    return sb, instr


def test_resume_loop_continues_until_stop_token(tmp_path: Path) -> None:
    """timeout_seconds>0: keep resuming the SAME session until the model
    emits the stop token. Round 1 has no stop token → resume; round 2 emits
    it → stop. The resume round must pass ``resume=<session_id>``."""
    agent = ClaudeAgent(model="claude-opus-4-7", timeout_seconds=600)
    sb, instr = _sandbox(tmp_path)

    rounds: list[dict] = []

    async def fake_query(*, prompt, options):
        rounds.append({"prompt": prompt, "resume": getattr(options, "resume", None)})
        if len(rounds) == 1:
            yield _assistant("working on it, not done yet")
            yield _result(0.5)
        else:
            yield _assistant(f"all markers filled, build clean {_STOP_TOKEN}")
            yield _result(0.3)

    with patch("vero.generation.agents.claude.query", side_effect=fake_query):
        result = agent.run(sandbox_dir=sb, instruction_file=instr)

    assert len(rounds) == 2, "should resume once, then stop on token"
    assert rounds[0]["resume"] is None, "round 1 is a fresh session"
    assert rounds[1]["resume"] == "sess-1", "round 2 resumes the SAME session"
    assert result.extra.get("stopped_by_token") is True
    assert result.extra.get("killed_by_timeout") is False
    assert result.extra.get("rounds") == 2
    # cost accumulates across rounds
    assert abs((result.total_cost_usd or 0) - 0.8) < 1e-9


def test_resume_loop_single_shot_when_no_timeout(tmp_path: Path) -> None:
    """timeout_seconds==0: legacy single query(), no resume even without a
    stop token."""
    agent = ClaudeAgent(model="claude-opus-4-7", timeout_seconds=0)
    sb, instr = _sandbox(tmp_path)

    calls = {"n": 0}

    async def fake_query(*, prompt, options):
        calls["n"] += 1
        yield _assistant("did some work, no stop token")
        yield _result(0.4)

    with patch("vero.generation.agents.claude.query", side_effect=fake_query):
        result = agent.run(sandbox_dir=sb, instruction_file=instr)

    assert calls["n"] == 1, "no timeout ⇒ exactly one round"
    assert result.extra.get("rounds") == 1
    assert result.extra.get("killed_by_timeout") is False


def test_resume_loop_stops_when_no_session_id(tmp_path: Path) -> None:
    """If a round yields no session id, we can't resume — end cleanly rather
    than loop forever."""
    agent = ClaudeAgent(model="claude-opus-4-7", timeout_seconds=600)
    sb, instr = _sandbox(tmp_path)

    calls = {"n": 0}

    async def fake_query(*, prompt, options):
        calls["n"] += 1
        m = _assistant("no session here", session_id="")
        yield m
        r = _result(0.2, session_id="")
        yield r

    with patch("vero.generation.agents.claude.query", side_effect=fake_query):
        result = agent.run(sandbox_dir=sb, instruction_file=instr)

    assert calls["n"] == 1, "no session id ⇒ cannot resume ⇒ one round"
    assert result.extra.get("stopped_by_token") is False
