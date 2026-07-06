"""Tests for GeminiAgent — command construction, per-sandbox setup, event routing.

No subprocess spawn; we just verify the pure pieces.
"""

from __future__ import annotations

import json
from pathlib import Path

from vero.generation.agents.event_log import EventLogger
from vero.generation.agents.gemini import GeminiAgent

# ─── _build_cmd ───────────────────────────────────────────────────


def test_build_cmd_default_sandbox_off() -> None:
    cmd = GeminiAgent(model="gemini-3.1-pro-preview")._build_cmd()
    assert cmd[0] == "gemini"
    # Prompt is fed by _spawn_and_stream (via -p or stdin), not _build_cmd.
    assert "-p" not in cmd
    assert "--output-format" in cmd
    i = cmd.index("--output-format")
    assert cmd[i + 1] == "stream-json"
    assert "-m" in cmd
    assert "gemini-3.1-pro-preview" in cmd
    assert "--approval-mode" in cmd
    i = cmd.index("--approval-mode")
    assert cmd[i + 1] == "yolo"
    # sandbox_mode="off" → no --sandbox flag emitted
    assert "--sandbox" not in cmd


def test_build_cmd_sandbox_flag_is_bare_boolean() -> None:
    # Real CLI: -s/--sandbox is boolean; backend comes from GEMINI_SANDBOX env.
    cmd = GeminiAgent(sandbox_mode="docker")._build_cmd()
    assert "--sandbox" in cmd
    # No backend name on the CLI — the next token (if any) should not be "docker".
    i = cmd.index("--sandbox")
    assert i == len(cmd) - 1 or cmd[i + 1].startswith("-")


def test_prepare_env_sets_gemini_sandbox_backend(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setenv("GEMINI_AGENT_API_KEY", "sk-fake")
    env = GeminiAgent(sandbox_mode="podman")._prepare_env(tmp_path)
    assert env["GEMINI_SANDBOX"] == "podman"


def test_prepare_env_omits_gemini_sandbox_when_off(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setenv("GEMINI_AGENT_API_KEY", "sk-fake")
    monkeypatch.delenv("GEMINI_SANDBOX", raising=False)
    env = GeminiAgent(sandbox_mode="off")._prepare_env(tmp_path)
    assert "GEMINI_SANDBOX" not in env


def test_build_cmd_approval_mode_override() -> None:
    cmd = GeminiAgent(approval_mode="auto_edit")._build_cmd()
    i = cmd.index("--approval-mode")
    assert cmd[i + 1] == "auto_edit"


def test_build_cmd_config_overrides_not_leaked_as_flags() -> None:
    # config_overrides are reserved for future settings.json injection;
    # they must not leak into the CLI as -c flags.
    cmd = GeminiAgent(config_overrides=["tools.core=edit,grep"])._build_cmd()
    assert "-c" not in cmd


# ─── _prepare_gemini_home ─────────────────────────────────────────


def _log(sandbox: Path) -> EventLogger:
    return EventLogger(agent="gemini", sandbox_dir=sandbox, mirror_to_stderr=False)


def test_prepare_gemini_home_writes_settings(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setenv("GEMINI_AGENT_API_KEY", "sk-fake")
    sandbox = tmp_path / "sb"
    sandbox.mkdir()
    log = _log(sandbox)
    try:
        home = GeminiAgent()._prepare_gemini_home(sandbox, log)
    finally:
        log.close()

    settings = json.loads((home / "settings.json").read_text())
    assert settings["model"]["name"] == "gemini-3.1-pro-preview"
    assert settings["general"]["defaultApprovalMode"] == "yolo"
    # Do not write a .env inside GEMINI_CLI_HOME — CLI would auto-load it.
    assert not (home / ".env").exists()


def test_prepare_gemini_home_scrubs_project_gemini_dir(
    tmp_path: Path, monkeypatch
) -> None:
    monkeypatch.setenv("GEMINI_AGENT_API_KEY", "sk-fake")
    sandbox = tmp_path / "sb"
    sandbox.mkdir()
    leak = sandbox / ".gemini"
    leak.mkdir()
    (leak / "system.md").write_text("HIJACKED SYSTEM PROMPT")
    log = _log(sandbox)
    try:
        GeminiAgent()._prepare_gemini_home(sandbox, log)
    finally:
        log.close()
    assert not leak.exists(), "project-level .gemini should have been scrubbed"


def test_prepare_gemini_home_respects_custom_model(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setenv("GEMINI_AGENT_API_KEY", "sk-fake")
    sandbox = tmp_path / "sb"
    sandbox.mkdir()
    log = _log(sandbox)
    try:
        home = GeminiAgent(model="gemini-2.5-flash")._prepare_gemini_home(sandbox, log)
    finally:
        log.close()
    settings = json.loads((home / "settings.json").read_text())
    assert settings["model"]["name"] == "gemini-2.5-flash"


# ─── _prepare_env ─────────────────────────────────────────────────


def test_prepare_env_injects_api_key_and_base_url(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.delenv("GEMINI_API_KEY", raising=False)
    monkeypatch.delenv("GOOGLE_API_KEY", raising=False)
    monkeypatch.delenv("GEMINI_AGENT_API_KEY", raising=False)
    monkeypatch.delenv("GEMINI_AGENT_BASE_URL", raising=False)
    monkeypatch.delenv("GOOGLE_GEMINI_BASE_URL", raising=False)
    monkeypatch.setenv("LLM_API_KEY", "sk-litellm")
    monkeypatch.setenv("LLM_API_BASE", "https://litellm.example.com")
    env = GeminiAgent()._prepare_env(tmp_path)
    assert env["GEMINI_API_KEY"] == "sk-litellm"
    assert env["GOOGLE_GEMINI_BASE_URL"] == "https://litellm.example.com"
    assert env["GEMINI_CLI_HOME"] == str(tmp_path)


def test_prepare_env_scrubs_claude_vars(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setenv("CLAUDECODE", "1")
    monkeypatch.setenv("CLAUDE_CODE_ENTRYPOINT", "x")
    monkeypatch.setenv("GEMINI_AGENT_API_KEY", "sk-fake")
    env = GeminiAgent()._prepare_env(tmp_path)
    assert "CLAUDECODE" not in env
    assert "CLAUDE_CODE_ENTRYPOINT" not in env


def test_prepare_env_agent_api_key_overrides_litellm(
    tmp_path: Path, monkeypatch
) -> None:
    # GEMINI_AGENT_API_KEY is the explicit override; it must win even
    # when LLM_API_KEY is also set (same priority rule as codex).
    monkeypatch.setenv("GEMINI_AGENT_API_KEY", "sk-explicit")
    monkeypatch.setenv("LLM_API_KEY", "sk-litellm")
    env = GeminiAgent()._prepare_env(tmp_path)
    assert env["GEMINI_API_KEY"] == "sk-explicit"


# ─── _route_event ─────────────────────────────────────────────────


def _events(path: Path) -> list[dict]:
    return [
        json.loads(ln)
        for ln in (path / "agent_events.jsonl").read_text().splitlines()
        if ln
    ]


def _fresh_state() -> dict:
    return {
        "turns": 0,
        "ok": True,
        "usage": {},
        "last_error": None,
        "last_event_type": None,
    }


def test_route_init_emits_raw(tmp_path: Path) -> None:
    agent = GeminiAgent()
    log = _log(tmp_path)
    state = _fresh_state()
    agent._route_event({"type": "init", "session_id": "s42"}, log, state)
    log.close()
    ev = _events(tmp_path)
    assert any(e["kind"] == "raw" and e.get("ev") == "gemini_init" for e in ev)


def test_route_assistant_message_maps_to_text(tmp_path: Path) -> None:
    agent = GeminiAgent()
    log = _log(tmp_path)
    state = _fresh_state()
    agent._route_event(
        {"type": "message", "role": "assistant", "content": "done"}, log, state
    )
    log.close()
    ev = _events(tmp_path)
    text_events = [e for e in ev if e["kind"] == "text"]
    assert len(text_events) == 1
    assert text_events[0]["text"] == "done"
    assert state["turns"] == 1


def test_route_user_message_does_not_bump_turns(tmp_path: Path) -> None:
    agent = GeminiAgent()
    log = _log(tmp_path)
    state = _fresh_state()
    agent._route_event({"type": "message", "role": "user", "content": "hi"}, log, state)
    log.close()
    assert state["turns"] == 0


def test_route_tool_use_and_result(tmp_path: Path) -> None:
    agent = GeminiAgent()
    log = _log(tmp_path)
    state = _fresh_state()
    agent._route_event(
        {
            "type": "tool_use",
            "name": "write_file",
            "input": {"path": "x.lean"},
            "id": "t1",
        },
        log,
        state,
    )
    agent._route_event(
        {
            "type": "tool_result",
            "tool_use_id": "t1",
            "is_error": False,
            "content": "ok",
        },
        log,
        state,
    )
    log.close()
    ev = _events(tmp_path)
    assert any(e["kind"] == "tool_use" and e["name"] == "write_file" for e in ev)
    assert any(e["kind"] == "tool_result" and e["is_error"] is False for e in ev)


def test_route_error_sets_ok_false(tmp_path: Path) -> None:
    agent = GeminiAgent()
    log = _log(tmp_path)
    state = _fresh_state()
    agent._route_event({"type": "error", "message": "quota exceeded"}, log, state)
    log.close()
    assert state["ok"] is False
    assert "quota exceeded" in (state["last_error"] or "")


def test_route_result_populates_usage_from_stats(tmp_path: Path) -> None:
    agent = GeminiAgent()
    log = _log(tmp_path)
    state = _fresh_state()
    agent._route_event(
        {
            "type": "result",
            "stats": {"token_usage": {"input_tokens": 100, "output_tokens": 50}},
        },
        log,
        state,
    )
    log.close()
    assert state["usage"] == {"input_tokens": 100, "output_tokens": 50}


def test_route_result_populates_usage_from_flat_usage(tmp_path: Path) -> None:
    # Alternate shape: older docs / some builds emit usage at top level.
    agent = GeminiAgent()
    log = _log(tmp_path)
    state = _fresh_state()
    agent._route_event(
        {"type": "result", "usage": {"input_tokens": 10, "output_tokens": 5}},
        log,
        state,
    )
    log.close()
    assert state["usage"] == {"input_tokens": 10, "output_tokens": 5}


def test_route_unknown_event_falls_through_to_raw(tmp_path: Path) -> None:
    agent = GeminiAgent()
    log = _log(tmp_path)
    state = _fresh_state()
    agent._route_event({"type": "some_future_event", "payload": "x"}, log, state)
    log.close()
    ev = _events(tmp_path)
    assert any(e["kind"] == "raw" and e.get("ev") == "gemini_unknown" for e in ev)
