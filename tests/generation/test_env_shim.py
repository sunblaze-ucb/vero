"""Tests for `vero.generation.agents.env_shim`."""

from __future__ import annotations

import json
import os
from pathlib import Path

from vero.generation.agents.env_shim import AgentEnvShim, shim_from_config


def test_materialize_writes_dotfiles(tmp_path: Path) -> None:
    shim = AgentEnvShim(
        kind="claude",
        sandbox_dir=tmp_path,
        env_declared={"ANTHROPIC_API_KEY": "sk-test"},
        dotfiles=[
            {"target": "settings.json", "content": '{"model": "sonnet"}'},
            {"target": "nested/config.toml", "content": "foo = 1"},
        ],
    )
    shim.materialize()
    assert (
        tmp_path / ".agent/claude/settings.json"
    ).read_text() == '{"model": "sonnet"}'
    assert (tmp_path / ".agent/claude/nested/config.toml").read_text() == "foo = 1"


def test_materialize_idempotent(tmp_path: Path) -> None:
    shim = AgentEnvShim(
        kind="codex",
        sandbox_dir=tmp_path,
        dotfiles=[{"target": "config.toml", "content": "v=1"}],
    )
    shim.materialize()
    shim.dotfiles[0]["content"] = "v=2"
    shim.materialize()
    assert (tmp_path / ".agent/codex/config.toml").read_text() == "v=2"


def test_build_env_merges_overrides(tmp_path: Path) -> None:
    shim = AgentEnvShim(
        kind="claude",
        sandbox_dir=tmp_path,
        env_declared={"FOO": "bar", "EMPTY": "", "NULL_OK": "present"},
    )
    base = {"BAZ": "qux", "FOO": "old"}
    env = shim.build_env(base=base)
    assert env["FOO"] == "bar"
    assert env["BAZ"] == "qux"
    assert env["NULL_OK"] == "present"
    # Empty values are skipped (reflects OmegaConf fallback when no source
    # env var is defined).
    assert "EMPTY" not in env


def test_build_env_does_not_mutate_base(tmp_path: Path) -> None:
    shim = AgentEnvShim(
        kind="claude",
        sandbox_dir=tmp_path,
        env_declared={"FOO": "new"},
    )
    base = {"FOO": "old"}
    shim.build_env(base=base)
    assert base["FOO"] == "old"


def test_scoped_environ_restores_prior(tmp_path: Path) -> None:
    existing = os.environ.get("VERO_TEST_VAR")
    os.environ["VERO_TEST_VAR"] = "outer"
    try:
        shim = AgentEnvShim(
            kind="claude",
            sandbox_dir=tmp_path,
            env_declared={"VERO_TEST_VAR": "inner", "VERO_NEW_VAR": "fresh"},
        )
        with shim.scoped_environ():
            assert os.environ["VERO_TEST_VAR"] == "inner"
            assert os.environ["VERO_NEW_VAR"] == "fresh"
        # Restored
        assert os.environ["VERO_TEST_VAR"] == "outer"
        assert "VERO_NEW_VAR" not in os.environ
    finally:
        if existing is None:
            os.environ.pop("VERO_TEST_VAR", None)
        else:
            os.environ["VERO_TEST_VAR"] = existing
        os.environ.pop("VERO_NEW_VAR", None)


def test_scoped_environ_restores_on_exception(tmp_path: Path) -> None:
    """Env must be restored even when the body raises."""
    os.environ.pop("VERO_EXC_VAR", None)
    shim = AgentEnvShim(
        kind="claude",
        sandbox_dir=tmp_path,
        env_declared={"VERO_EXC_VAR": "inside"},
    )
    try:
        with shim.scoped_environ():
            assert os.environ["VERO_EXC_VAR"] == "inside"
            raise RuntimeError("boom")
    except RuntimeError:
        pass
    assert "VERO_EXC_VAR" not in os.environ


def test_shim_from_config(tmp_path: Path) -> None:
    agent_cfg = {
        "kind": "claude",
        "model": "sonnet",
        "env": {
            "ANTHROPIC_API_KEY": "sk-test",
            "ANTHROPIC_BASE_URL": "",  # empty string → skipped
        },
        "dotfiles": [
            {"target": "settings.json", "content": "{}"},
        ],
    }
    shim = shim_from_config("claude", tmp_path, agent_cfg)
    assert shim.kind == "claude"
    assert shim.env_declared == {
        "ANTHROPIC_API_KEY": "sk-test",
        "ANTHROPIC_BASE_URL": "",
    }
    assert len(shim.dotfiles) == 1
    # Empty-string values are filtered out by build_env, not by the factory.
    env = shim.build_env(base={})
    assert env == {"ANTHROPIC_API_KEY": "sk-test"}


def test_shim_from_config_missing_sections(tmp_path: Path) -> None:
    """When env:/dotfiles: are absent, shim still constructs cleanly."""
    agent_cfg = {"kind": "codex"}
    shim = shim_from_config("codex", tmp_path, agent_cfg)
    assert shim.env_declared == {}
    assert shim.dotfiles == []
    assert shim.config_files == []
    # build_env is a passthrough when nothing is declared
    env = shim.build_env(base={"PATH": "/usr/bin"})
    assert env == {"PATH": "/usr/bin"}


def test_shim_writes_json_config_with_proper_format(tmp_path: Path) -> None:
    """JSON config_files entries serialize the dict to <sandbox>/.<kind>/<target>."""
    shim = AgentEnvShim(
        kind="claude",
        sandbox_dir=tmp_path,
        env_declared={},
        config_files=[
            {
                "target": "settings.json",
                "content_type": "json",
                "content": {"env": {"ANTHROPIC_BASE_URL": "https://example/v1"}},
            }
        ],
    )
    config_dir = shim.materialize_config_dir()
    assert config_dir == tmp_path / ".claude"
    settings = json.loads((config_dir / "settings.json").read_text())
    assert settings["env"]["ANTHROPIC_BASE_URL"] == "https://example/v1"


def test_shim_writes_toml_raw_config(tmp_path: Path) -> None:
    """toml_raw entries are written verbatim, no parsing or escaping."""
    shim = AgentEnvShim(
        kind="codex",
        sandbox_dir=tmp_path,
        env_declared={},
        config_files=[
            {
                "target": "config.toml",
                "content_type": "toml_raw",
                "content": 'model = "x"\n[model_providers.foo]\nbase_url = "y"\n',
            }
        ],
    )
    config_dir = shim.materialize_config_dir()
    assert config_dir == tmp_path / ".codex"
    text = (config_dir / "config.toml").read_text()
    assert 'model = "x"' in text
    assert "[model_providers.foo]" in text


def test_shim_skips_config_dir_when_no_config_files(tmp_path: Path) -> None:
    """Empty config_files → return None, signal "use user's global config dir"."""
    shim = AgentEnvShim(
        kind="claude", sandbox_dir=tmp_path, env_declared={}, config_files=[]
    )
    assert shim.materialize_config_dir() is None
    assert not (tmp_path / ".claude").exists()


# ─── credential-hole warning ───────────────────────────────────────


def test_shim_warns_on_empty_required_auth_key_in_env(tmp_path: Path, caplog) -> None:
    """Empty OPENROUTER_API_KEY in env_declared → loud warning at shim build.

    Mirrors the `credentials=openrouter` profile + missing OR key in
    .env case: the OmegaConf interpolation collapses to "", the shim
    drops it from env, and the codex / claude subprocess later fails
    with a 401. Warning makes the cause discoverable.
    """
    from loguru import logger

    sink_records: list[str] = []
    sink_id = logger.add(lambda msg: sink_records.append(str(msg)), level="WARNING")
    try:
        shim_from_config(
            "codex",
            tmp_path,
            {"env": {"OPENROUTER_API_KEY": ""}, "config_files": []},
        )
    finally:
        logger.remove(sink_id)
    joined = "\n".join(sink_records)
    assert "credential hole" in joined.lower()
    assert "OPENROUTER_API_KEY" in joined


def test_shim_warns_on_empty_settings_json_env_block(tmp_path: Path) -> None:
    """Empty OPENROUTER_API_KEY in settings.json env block → loud warning.

    Claude path: OmegaConf renders the auth token into both the
    process env block AND the settings.json env block. We catch
    holes in either site.
    """
    from loguru import logger

    sink_records: list[str] = []
    sink_id = logger.add(lambda msg: sink_records.append(str(msg)), level="WARNING")
    try:
        shim_from_config(
            "claude",
            tmp_path,
            {
                "env": {},
                "config_files": [
                    {
                        "target": "settings.json",
                        "content_type": "json",
                        "content": {
                            "env": {
                                "ANTHROPIC_AUTH_TOKEN": "",
                                "ANTHROPIC_BASE_URL": "https://openrouter.ai/api/v1",
                            }
                        },
                    }
                ],
            },
        )
    finally:
        logger.remove(sink_id)
    joined = "\n".join(sink_records)
    assert "credential hole" in joined.lower()
    assert "ANTHROPIC_AUTH_TOKEN" in joined


def test_shim_no_warning_when_required_keys_resolve(
    tmp_path: Path,
) -> None:
    """Sanity: a fully-resolved env block must not emit the warning."""
    from loguru import logger

    sink_records: list[str] = []
    sink_id = logger.add(lambda msg: sink_records.append(str(msg)), level="WARNING")
    try:
        shim_from_config(
            "codex",
            tmp_path,
            {"env": {"OPENROUTER_API_KEY": "sk-real"}, "config_files": []},
        )
    finally:
        logger.remove(sink_id)
    joined = "\n".join(sink_records)
    assert "credential hole" not in joined.lower()
