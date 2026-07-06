"""Tests for the shared EventLogger."""

from __future__ import annotations

import json
from pathlib import Path

import pytest

from vero.generation.agents.event_log import EventLogger


def _lines(path: Path) -> list[dict]:
    return [json.loads(ln) for ln in path.read_text().splitlines() if ln.strip()]


def test_logger_writes_jsonl_and_text(tmp_path: Path) -> None:
    with EventLogger(agent="test", sandbox_dir=tmp_path, mirror_to_stderr=False) as log:
        log.run_start(model="x", max_turns=7)
        log.thinking("think hard")
        log.text("hello")
        log.tool_use(name="Read", input={"file_path": "/x/y"}, id="t1")
        log.tool_result(is_error=False, content="ok", tool_use_id="t1")
        log.run_end(ok=True, num_turns=3, total_cost_usd=0.42, usage={"in": 10})

    events = _lines(log.jsonl_path)
    kinds = [e["kind"] for e in events]
    assert kinds == [
        "run_start",
        "thinking",
        "text",
        "tool_use",
        "tool_result",
        "run_end",
    ]
    text = log.text_path.read_text().splitlines()
    assert len(text) == len(events)
    assert "[thinking]" in text[1]
    assert "[tool_use]" in text[3]


def test_logger_captures_exception_as_run_error(tmp_path: Path) -> None:
    log = EventLogger(agent="test", sandbox_dir=tmp_path, mirror_to_stderr=False)
    with pytest.raises(RuntimeError):
        with log:
            log.text("first event")
            raise RuntimeError("boom")

    events = _lines(log.jsonl_path)
    kinds = [e["kind"] for e in events]
    assert "run_error" in kinds
    err_event = [e for e in events if e["kind"] == "run_error"][0]
    assert "boom" in err_event["message"]
    assert err_event.get("error_type") == "RuntimeError"
    assert "traceback" in err_event


def test_logger_jsonl_has_full_content_no_truncation(tmp_path: Path) -> None:
    huge = "x" * 20_000
    with EventLogger(
        agent="test",
        sandbox_dir=tmp_path,
        mirror_to_stderr=False,
        text_truncate=100,
    ) as log:
        log.text(huge)

    [event] = [e for e in _lines(log.jsonl_path) if e["kind"] == "text"]
    assert event["text"] == huge
    # Text mirror truncates.
    text_mirror = log.text_path.read_text().splitlines()[0]
    assert len(text_mirror) < len(huge)
    assert "[+" in text_mirror  # truncation suffix


def test_logger_handles_non_json_serializable(tmp_path: Path) -> None:
    class Weird:
        def __init__(self):
            self.a = 1
            self._b = 2

    with EventLogger(agent="test", sandbox_dir=tmp_path, mirror_to_stderr=False) as log:
        log.tool_use(name="thing", input={"obj": Weird()})

    events = _lines(log.jsonl_path)
    tool_ev = [e for e in events if e["kind"] == "tool_use"][0]
    # Fallback serialization kicks in for Weird — check we got SOMETHING usable.
    assert "obj" in tool_ev["input"]
