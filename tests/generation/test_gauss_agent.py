"""Tests for GaussAgent — command construction, per-sandbox setup, prompt
nudge, trajectory replay.

No subprocess spawn; we just verify the pure pieces.
"""

from __future__ import annotations

import json
from pathlib import Path

from vero.generation.agents.event_log import EventLogger
from vero.generation.agents.gauss import GaussAgent

# ─── _build_cmd ───────────────────────────────────────────────────


def test_build_cmd_default_shape() -> None:
    cmd = GaussAgent()._build_cmd(prompt="hello")
    assert cmd[0] == "gauss"
    assert cmd[1] == "chat"
    assert "-q" in cmd
    i = cmd.index("-q")
    assert cmd[i + 1] == "hello"
    assert "--quiet" in cmd
    assert "--yolo" in cmd
    assert "--provider" in cmd
    i = cmd.index("--provider")
    assert cmd[i + 1] == "auto"


def test_build_cmd_with_model_and_worktree() -> None:
    cmd = GaussAgent(model="claude-sonnet-4-6", worktree=True)._build_cmd(prompt="x")
    assert "-m" in cmd and "claude-sonnet-4-6" in cmd
    assert "--worktree" in cmd


def test_build_cmd_yolo_off() -> None:
    cmd = GaussAgent(yolo=False)._build_cmd(prompt="x")
    assert "--yolo" not in cmd


def test_build_cmd_does_not_emit_save_trajectories_flag() -> None:
    # `gauss chat` v0.2.2 has no --save-trajectories flag (SDK-only). Setting
    # save_trajectories=True on the dataclass must NOT leak a flag that the
    # CLI would reject — trajectory replay is post-hoc best-effort only.
    cmd = GaussAgent(save_trajectories=True)._build_cmd(prompt="x")
    assert "--save-trajectories" not in cmd


def test_build_cmd_provider_override() -> None:
    cmd = GaussAgent(provider="anthropic")._build_cmd(prompt="x")
    i = cmd.index("--provider")
    assert cmd[i + 1] == "anthropic"


# ─── _build_prompt (in-agent nudge) ───────────────────────────────


def test_build_prompt_appends_nudge() -> None:
    text = GaussAgent()._build_prompt("Read INSTRUCTION.md and do the task.")
    assert "/prove" in text
    assert "/autoformalize" in text
    assert text.startswith("Read INSTRUCTION.md and do the task.")


# ─── _prepare_gauss_home ──────────────────────────────────────────


def _log(sandbox: Path) -> EventLogger:
    return EventLogger(agent="gauss", sandbox_dir=sandbox, mirror_to_stderr=False)


def test_prepare_gauss_home_writes_env_for_auto_provider(
    tmp_path: Path, monkeypatch
) -> None:
    # provider=auto → OPENROUTER_API_KEY slot
    for k in (
        "OPENROUTER_API_KEY",
        "ANTHROPIC_API_KEY",
        "OPENAI_API_KEY",
        "LLM_API_KEY",
    ):
        monkeypatch.delenv(k, raising=False)
    monkeypatch.setenv("GAUSS_AGENT_API_KEY", "sk-gauss")
    sandbox = tmp_path / "sb"
    sandbox.mkdir()
    log = _log(sandbox)
    try:
        home = GaussAgent(provider="auto")._prepare_gauss_home(sandbox, log)
    finally:
        log.close()
    env_text = (home / ".env").read_text()
    assert "OPENROUTER_API_KEY=sk-gauss" in env_text


def test_prepare_gauss_home_writes_env_for_anthropic_provider(
    tmp_path: Path, monkeypatch
) -> None:
    for k in ("ANTHROPIC_API_KEY", "LLM_API_KEY", "GAUSS_AGENT_API_KEY"):
        monkeypatch.delenv(k, raising=False)
    monkeypatch.setenv("ANTHROPIC_API_KEY", "sk-ant")
    sandbox = tmp_path / "sb"
    sandbox.mkdir()
    log = _log(sandbox)
    try:
        home = GaussAgent(provider="anthropic")._prepare_gauss_home(sandbox, log)
    finally:
        log.close()
    env_text = (home / ".env").read_text()
    assert "ANTHROPIC_API_KEY=sk-ant" in env_text


def test_prepare_gauss_home_writes_base_url_when_present(
    tmp_path: Path, monkeypatch
) -> None:
    monkeypatch.setenv("GAUSS_AGENT_API_KEY", "sk")
    monkeypatch.setenv("LLM_API_BASE", "https://litellm.example.com")
    sandbox = tmp_path / "sb"
    sandbox.mkdir()
    log = _log(sandbox)
    try:
        home = GaussAgent()._prepare_gauss_home(sandbox, log)
    finally:
        log.close()
    env_text = (home / ".env").read_text()
    assert "OPENAI_BASE_URL=https://litellm.example.com" in env_text


# ─── _prepare_env ─────────────────────────────────────────────────


def test_prepare_env_sets_gauss_home_and_scrubs_claude_vars(
    tmp_path: Path, monkeypatch
) -> None:
    monkeypatch.setenv("CLAUDECODE", "1")
    monkeypatch.setenv("CLAUDE_CODE_ENTRYPOINT", "x")
    monkeypatch.setenv("GAUSS_AGENT_API_KEY", "sk-gauss")
    env = GaussAgent()._prepare_env(tmp_path)
    assert env["GAUSS_HOME"] == str(tmp_path)
    assert "CLAUDECODE" not in env
    assert "CLAUDE_CODE_ENTRYPOINT" not in env


# ─── trajectory replay ───────────────────────────────────────────


def test_replay_trajectory_emits_text_and_tool_events(tmp_path: Path) -> None:
    # ShareGPT JSONL: one line per conversation, with a `conversations` array
    # of {from, value} entries. Tool calls are serialized as text blocks.
    line = json.dumps(
        {
            "conversations": [
                {"from": "human", "value": "do the thing"},
                {"from": "gpt", "value": "thinking about it"},
                {"from": "tool", "value": "ran bash -c 'ls'"},
            ]
        }
    )
    path = tmp_path / "traj.jsonl"
    path.write_text(line + "\n")
    log = _log(tmp_path)
    try:
        GaussAgent()._replay_trajectory(path, log)
    finally:
        log.close()
    events = [
        json.loads(ln)
        for ln in (tmp_path / "agent_events.jsonl").read_text().splitlines()
        if ln
    ]
    kinds = [e["kind"] for e in events]
    assert "text" in kinds
    assert "tool_use" in kinds


def test_replay_trajectory_missing_file_is_noop(tmp_path: Path) -> None:
    log = _log(tmp_path)
    try:
        GaussAgent()._replay_trajectory(tmp_path / "does-not-exist", log)
    finally:
        log.close()
    # No exception. The JSONL file should exist but be empty (just the
    # logger's own close-time artifacts, if any).
    txt = (tmp_path / "agent_events.jsonl").read_text()
    assert "gauss_trajectory_parse_failed" not in txt


def test_replay_trajectory_malformed_json_logs_error(tmp_path: Path) -> None:
    path = tmp_path / "bad.jsonl"
    path.write_text("{not json}\n")
    log = _log(tmp_path)
    try:
        GaussAgent()._replay_trajectory(path, log)
    finally:
        log.close()
    txt = (tmp_path / "agent_events.jsonl").read_text()
    assert "gauss_trajectory_parse_failed" in txt
