"""Tests for BaseAgent lifecycle: logging, error wrapping, timeout."""

from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path

from vero.generation.agents.base import BaseAgent, RunOutcome


def _make_instruction(dir: Path) -> Path:
    instr = dir / "INSTRUCTION.md"
    instr.write_text("do work")
    return instr


def _events(sandbox: Path) -> list[dict]:
    return [
        json.loads(ln)
        for ln in (sandbox / "agent_events.jsonl").read_text().splitlines()
        if ln
    ]


@dataclass
class _FakeAgent(BaseAgent):
    name: str = "fake"
    outcome: RunOutcome | None = None
    raise_exc: BaseException | None = None

    def _run_inner(self, *, event_log, sandbox_dir, instruction_file):
        event_log.text("working")
        event_log.tool_use(name="Read", input={"path": "x"})
        event_log.tool_result(is_error=False, content="ok")
        if self.raise_exc is not None:
            raise self.raise_exc
        return self.outcome or RunOutcome(
            ok=True, num_turns=3, total_cost_usd=1.5, usage={"input_tokens": 42}
        )


def test_base_agent_happy_path_writes_structured_log(tmp_path: Path) -> None:
    sandbox = tmp_path / "sb"
    sandbox.mkdir()
    instr = _make_instruction(sandbox)

    agent = _FakeAgent()
    result = agent.run(sandbox_dir=sandbox, instruction_file=instr)

    assert result.ok
    assert result.num_turns == 3
    assert result.total_cost_usd == 1.5
    assert result.usage == {"input_tokens": 42}
    assert result.event_log_path == sandbox / "agent_events.jsonl"
    assert result.text_log_path == sandbox / "agent.log"

    events = _events(sandbox)
    kinds = [e["kind"] for e in events]
    assert kinds[0] == "run_start"
    assert "text" in kinds
    assert "tool_use" in kinds
    assert "tool_result" in kinds
    assert kinds[-1] == "run_end"
    end = events[-1]
    assert end["ok"] is True
    assert end["num_turns"] == 3
    assert end["total_cost_usd"] == 1.5


def test_base_agent_catches_inner_exception(tmp_path: Path) -> None:
    sandbox = tmp_path / "sb"
    sandbox.mkdir()
    instr = _make_instruction(sandbox)

    agent = _FakeAgent(raise_exc=RuntimeError("inner boom"))
    result = agent.run(sandbox_dir=sandbox, instruction_file=instr)

    assert result.ok is False
    assert "RuntimeError" in (result.error or "")
    assert "inner boom" in (result.error or "")

    events = _events(sandbox)
    # Should have a run_error and then run_end.
    kinds = [e["kind"] for e in events]
    assert "run_error" in kinds
    assert kinds[-1] == "run_end"


def test_base_agent_missing_instruction_raises(tmp_path: Path) -> None:
    sandbox = tmp_path / "sb"
    sandbox.mkdir()
    import pytest

    with pytest.raises(FileNotFoundError):
        _FakeAgent().run(sandbox_dir=sandbox, instruction_file=sandbox / "nope.md")


def test_run_end_carries_cost_and_usage_metadata(tmp_path: Path) -> None:
    """Every run_end event contains ``usage``, ``total_cost_usd``,
    ``computed_cost_usd``, ``sdk_cost_usd``, ``elapsed_seconds`` so that
    sweep aggregation can read uniform metadata regardless of backend."""
    sandbox = tmp_path / "sb"
    sandbox.mkdir()
    instr = _make_instruction(sandbox)

    outcome = RunOutcome(
        ok=True,
        num_turns=2,
        total_cost_usd=0.42,
        usage={"input_tokens": 1000, "output_tokens": 200},
        extra={"computed_cost_usd": 0.42, "sdk_cost_usd": 0.5, "exit_code": 0},
    )
    agent = _FakeAgent(outcome=outcome)
    agent.run(sandbox_dir=sandbox, instruction_file=instr)

    events = _events(sandbox)
    end = events[-1]
    assert end["kind"] == "run_end"
    assert end["ok"] is True
    assert end["num_turns"] == 2
    assert end["total_cost_usd"] == 0.42
    assert end["usage"] == {"input_tokens": 1000, "output_tokens": 200}
    assert end["computed_cost_usd"] == 0.42
    assert end["sdk_cost_usd"] == 0.5
    assert "elapsed_seconds" in end


def test_run_end_metadata_when_extra_missing(tmp_path: Path) -> None:
    """Backends that don't surface computed/SDK costs (gauss/gemini today)
    still get a stable run_end shape — the keys appear with None."""
    sandbox = tmp_path / "sb"
    sandbox.mkdir()
    instr = _make_instruction(sandbox)

    outcome = RunOutcome(
        ok=True,
        num_turns=1,
        total_cost_usd=None,
        usage={},
        extra={},
    )
    _FakeAgent(outcome=outcome).run(sandbox_dir=sandbox, instruction_file=instr)

    end = _events(sandbox)[-1]
    assert end["computed_cost_usd"] is None
    assert end["sdk_cost_usd"] is None


def test_base_agent_timeout_fires(tmp_path: Path) -> None:
    """SIGALRM-based timeout raises into the inner run and is captured."""
    import time

    sandbox = tmp_path / "sb"
    sandbox.mkdir()
    instr = _make_instruction(sandbox)

    @dataclass
    class _SlowAgent(BaseAgent):
        name: str = "slow"
        timeout_seconds: int = 1

        def _run_inner(self, *, event_log, sandbox_dir, instruction_file):
            event_log.text("starting slow work")
            time.sleep(3)
            return RunOutcome(ok=True)

    result = _SlowAgent().run(sandbox_dir=sandbox, instruction_file=instr)
    assert result.ok is False
    assert "timeout" in (result.error or "").lower()
    events = _events(sandbox)
    assert any(e["kind"] == "run_error" for e in events)
