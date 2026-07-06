"""Tests for CodexAgent — command construction + JSONL event routing.

No subprocess spawn; we just verify the pure pieces (command-line shape,
event-routing logic).
"""

from __future__ import annotations

import json
from pathlib import Path

from vero.generation.agents.codex import CodexAgent
from vero.generation.agents.env_shim import AgentEnvShim
from vero.generation.agents.event_log import EventLogger


def test_build_cmd_workspace_write_default() -> None:
    cmd = CodexAgent(model="gpt-5-codex")._build_cmd()
    assert cmd[0] == "codex"
    assert "exec" in cmd and "--json" in cmd
    assert "--full-auto" in cmd
    assert "--skip-git-repo-check" in cmd
    assert cmd[-1] == "-"
    assert "-m" in cmd and "gpt-5-codex" in cmd


def test_build_cmd_read_only() -> None:
    cmd = CodexAgent(sandbox_mode="read-only")._build_cmd()
    assert "--sandbox" in cmd
    i = cmd.index("--sandbox")
    assert cmd[i + 1] == "read-only"


def test_build_cmd_danger_full_access() -> None:
    cmd = CodexAgent(sandbox_mode="danger-full-access")._build_cmd()
    assert "--dangerously-bypass-approvals-and-sandbox" in cmd


def test_build_cmd_network_access_override() -> None:
    cmd = CodexAgent(network_access=True)._build_cmd()
    # -c sandbox_workspace_write.network_access=true
    assert "sandbox_workspace_write.network_access=true" in cmd


def test_build_cmd_config_overrides() -> None:
    cmd = CodexAgent(config_overrides=['model="o4"', "other=42"])._build_cmd()
    assert cmd.count("-c") >= 2
    assert 'model="o4"' in cmd
    assert "other=42" in cmd


def _log(tmp_path: Path) -> tuple[EventLogger, Path]:
    log = EventLogger(agent="codex", sandbox_dir=tmp_path, mirror_to_stderr=False)
    return log, tmp_path


def _events(path: Path) -> list[dict]:
    return [
        json.loads(ln)
        for ln in (path / "agent_events.jsonl").read_text().splitlines()
        if ln
    ]


def test_route_thread_and_turn_events(tmp_path: Path) -> None:
    agent = CodexAgent()
    log, sb = _log(tmp_path)
    state = {
        "turns": 0,
        "ok": True,
        "usage": {},
        "last_error": None,
        "last_event_type": None,
    }

    agent._route_event({"type": "thread.started", "thread_id": "t42"}, log, state)
    agent._route_event({"type": "turn.started"}, log, state)
    agent._route_event(
        {
            "type": "turn.completed",
            "usage": {
                "input_tokens": 100,
                "cached_input_tokens": 10,
                "output_tokens": 50,
            },
        },
        log,
        state,
    )
    log.close()

    events = _events(sb)
    ev_names = [e.get("ev") for e in events if e["kind"] == "raw"]
    assert "codex_thread_started" in ev_names
    assert "codex_turn_started" in ev_names
    assert "codex_turn_completed" in ev_names
    assert state["turns"] == 1
    assert state["usage"] == {
        "input_tokens": 100,
        "cached_input_tokens": 10,
        "output_tokens": 50,
    }


def test_route_agent_message_maps_to_text(tmp_path: Path) -> None:
    agent = CodexAgent()
    log, sb = _log(tmp_path)
    state = {
        "turns": 0,
        "ok": True,
        "usage": {},
        "last_error": None,
        "last_event_type": None,
    }

    agent._route_event(
        {
            "type": "item.completed",
            "item": {"id": "m1", "type": "agent_message", "text": "done"},
        },
        log,
        state,
    )
    log.close()

    events = _events(sb)
    text_events = [e for e in events if e["kind"] == "text"]
    assert len(text_events) == 1
    assert text_events[0]["text"] == "done"


def test_route_reasoning_maps_to_thinking(tmp_path: Path) -> None:
    agent = CodexAgent()
    log, sb = _log(tmp_path)
    state = {
        "turns": 0,
        "ok": True,
        "usage": {},
        "last_error": None,
        "last_event_type": None,
    }

    agent._route_event(
        {
            "type": "item.completed",
            "item": {"id": "r1", "type": "reasoning", "text": "planning"},
        },
        log,
        state,
    )
    log.close()

    events = _events(sb)
    assert any(e["kind"] == "thinking" and e["text"] == "planning" for e in events)


def test_route_command_execution_emits_tool_use_and_result(tmp_path: Path) -> None:
    agent = CodexAgent()
    log, sb = _log(tmp_path)
    state = {
        "turns": 0,
        "ok": True,
        "usage": {},
        "last_error": None,
        "last_event_type": None,
    }

    agent._route_event(
        {
            "type": "item.started",
            "item": {"id": "c1", "type": "command_execution", "command": "ls /src"},
        },
        log,
        state,
    )
    agent._route_event(
        {
            "type": "item.completed",
            "item": {
                "id": "c1",
                "type": "command_execution",
                "command": "ls /src",
                "status": "completed",
                "exit_code": 0,
                "aggregated_output": "a.lean\nb.lean\n",
            },
        },
        log,
        state,
    )
    log.close()

    events = _events(sb)
    tool_uses = [e for e in events if e["kind"] == "tool_use"]
    tool_results = [e for e in events if e["kind"] == "tool_result"]
    assert len(tool_uses) == 1 and tool_uses[0]["name"] == "bash"
    assert len(tool_results) == 1
    assert tool_results[0]["is_error"] is False
    assert tool_results[0]["content"]["exit_code"] == 0


def test_route_turn_failed_sets_ok_false(tmp_path: Path) -> None:
    agent = CodexAgent()
    log, sb = _log(tmp_path)
    state = {
        "turns": 0,
        "ok": True,
        "usage": {},
        "last_error": None,
        "last_event_type": None,
    }

    agent._route_event(
        {"type": "turn.failed", "error": {"message": "rate limited"}},
        log,
        state,
    )
    log.close()

    assert state["ok"] is False
    assert "rate limited" in (state["last_error"] or "")
    events = _events(sb)
    assert any(e["kind"] == "run_error" for e in events)


def test_prepare_codex_home_writes_files(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setenv("CODEX_AGENT_API_KEY", "sk-fake")
    monkeypatch.setenv("CODEX_AGENT_BASE_URL", "https://example.com/v1")
    sandbox = tmp_path / "sb"
    sandbox.mkdir()
    log = EventLogger(agent="codex", sandbox_dir=sandbox, mirror_to_stderr=False)
    try:
        home = CodexAgent()._prepare_codex_home(sandbox, log)
    finally:
        log.close()

    auth = json.loads((home / "auth.json").read_text())
    assert auth == {"OPENAI_API_KEY": "sk-fake"}
    config = (home / "config.toml").read_text()
    assert 'openai_base_url = "https://example.com/v1"' in config
    assert 'model_provider = "openai_http"' in config
    assert "[model_providers.openai_http]" in config
    assert 'env_key = "OPENAI_API_KEY"' in config


def test_prepare_env_scrubs_claude_vars(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setenv("CLAUDECODE", "1")
    monkeypatch.setenv("CLAUDE_CODE_ENTRYPOINT", "x")
    monkeypatch.setenv("CODEX_AGENT_API_KEY", "sk-fake2")
    sandbox = tmp_path
    log = EventLogger(agent="codex", sandbox_dir=sandbox, mirror_to_stderr=False)
    env = CodexAgent()._prepare_env(sandbox, log)
    assert "CLAUDECODE" not in env
    assert "CLAUDE_CODE_ENTRYPOINT" not in env
    assert env["CODEX_API_KEY"] == "sk-fake2"
    # When no shim is attached, CODEX_HOME falls back to the legacy
    # _prepare_codex_home dir under the sandbox.
    assert env["CODEX_HOME"] == str(sandbox / ".codex_home")


def test_prepare_env_empty_shim_copies_existing_global_codex_home(
    tmp_path: Path, monkeypatch
) -> None:
    global_home = tmp_path / "global-codex-home"
    global_home.mkdir()
    (global_home / "auth.json").write_text('{"OPENAI_API_KEY":"local"}')
    (global_home / "config.toml").write_text('web_search = "disabled"\n')
    (global_home / "state_5.sqlite").write_text("runtime")
    monkeypatch.setenv("CODEX_HOME", str(global_home))
    monkeypatch.delenv("CODEX_AGENT_API_KEY", raising=False)
    sandbox = tmp_path / "sandbox"
    sandbox.mkdir()
    agent = CodexAgent()
    agent.env_shim = AgentEnvShim(
        kind="codex",
        sandbox_dir=sandbox,
        env_declared={},
        config_files=[],
    )
    log = EventLogger(agent="codex", sandbox_dir=sandbox, mirror_to_stderr=False)
    try:
        env = agent._prepare_env(sandbox, log)
    finally:
        log.close()

    copied_home = sandbox / ".codex_local_home"
    assert env["CODEX_HOME"] == str(copied_home)
    assert (copied_home / "auth.json").read_text() == '{"OPENAI_API_KEY":"local"}'
    assert (copied_home / "config.toml").read_text() == 'web_search = "disabled"\n'
    assert not (copied_home / "state_5.sqlite").exists()
    assert not (sandbox / ".codex_home").exists()


def test_prepare_env_empty_shim_preserves_missing_global_codex_home(
    tmp_path: Path, monkeypatch
) -> None:
    missing_home = tmp_path / "missing-codex-home"
    monkeypatch.setenv("CODEX_HOME", str(missing_home))
    monkeypatch.delenv("CODEX_AGENT_API_KEY", raising=False)
    agent = CodexAgent()
    agent.env_shim = AgentEnvShim(
        kind="codex",
        sandbox_dir=tmp_path,
        env_declared={},
        config_files=[],
    )
    log = EventLogger(agent="codex", sandbox_dir=tmp_path, mirror_to_stderr=False)
    try:
        env = agent._prepare_env(tmp_path, log)
    finally:
        log.close()

    assert env["CODEX_HOME"] == str(missing_home)
    assert not (tmp_path / ".codex_local_home").exists()


# ─── Token-based cost (pricing) ─────────────────────────────────────


def _state(usage: dict, *, ok: bool = True, turns: int = 1) -> dict:
    return {
        "turns": turns,
        "ok": ok,
        "usage": usage,
        "last_error": None,
        "last_event_type": None,
    }


def test_build_outcome_known_model_carries_token_cost() -> None:
    """When model is in pricing.PRICING and usage non-empty, RunOutcome
    carries a non-None total_cost_usd computed from the pricing table."""
    import pytest

    agent = CodexAgent(model="gpt-5.5")
    state = _state(
        {
            "input_tokens": 1_000_000,
            "cached_input_tokens": 0,
            "output_tokens": 100_000,
        }
    )
    outcome = agent._build_outcome(
        state, exit_code=0, killed_by_timeout=False, stderr_chunks=[]
    )
    assert outcome.ok is True
    # gpt-5.5: $5/Mtok new + $30/Mtok output * 0.1 = $5 + $3 = $8.
    assert outcome.total_cost_usd == pytest.approx(8.0)
    assert outcome.extra["computed_cost_usd"] == pytest.approx(8.0)


def test_build_outcome_unknown_model_leaves_cost_none() -> None:
    """Unknown model: cost stays None (signals 'we don't know'), not 0.0."""
    agent = CodexAgent(model="not-a-real-model")
    state = _state({"input_tokens": 100, "output_tokens": 100})
    outcome = agent._build_outcome(
        state, exit_code=0, killed_by_timeout=False, stderr_chunks=[]
    )
    assert outcome.total_cost_usd is None
    assert outcome.extra.get("computed_cost_usd") is None


def test_build_outcome_no_model_leaves_cost_none() -> None:
    agent = CodexAgent(model=None)
    state = _state({"input_tokens": 100, "output_tokens": 100})
    outcome = agent._build_outcome(
        state, exit_code=0, killed_by_timeout=False, stderr_chunks=[]
    )
    assert outcome.total_cost_usd is None


def test_build_outcome_empty_usage_zero_cost() -> None:
    """Empty usage → cost is 0.0 for known models (not None)."""
    agent = CodexAgent(model="gpt-5.5")
    state = _state({})
    outcome = agent._build_outcome(
        state, exit_code=0, killed_by_timeout=False, stderr_chunks=[]
    )
    assert outcome.total_cost_usd == 0.0


def test_build_outcome_propagates_exit_code() -> None:
    agent = CodexAgent(model="gpt-5.5")
    state = _state({"input_tokens": 100, "output_tokens": 50}, ok=False)
    state["last_error"] = "exit=2"
    outcome = agent._build_outcome(
        state, exit_code=2, killed_by_timeout=False, stderr_chunks=["bad\n"]
    )
    assert outcome.ok is False
    assert outcome.error == "exit=2"
    assert outcome.extra["exit_code"] == 2
    assert outcome.stderr_tail == "bad\n"
