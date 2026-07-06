import shutil
from pathlib import Path

from vero.curation.agent import _build_codex_env


def test_local_codex_auth_uses_writable_copied_home(
    tmp_path: Path, monkeypatch
) -> None:
    source_home = tmp_path / "home"
    codex_home = source_home / ".codex"
    codex_home.mkdir(parents=True)
    (codex_home / "auth.json").write_text('{"token":"local"}', encoding="utf-8")
    (codex_home / "config.toml").write_text('model = "local"\n', encoding="utf-8")
    (codex_home / "rules").mkdir()
    (codex_home / "rules" / "default.rules").write_text("allow\n", encoding="utf-8")

    monkeypatch.setenv("HOME", str(source_home))
    monkeypatch.setenv("CODEX_API_KEY", "drained")
    monkeypatch.setenv("OPENAI_API_KEY", "drained")
    monkeypatch.setenv("LLM_API_KEY", "drained")

    env, temp_home = _build_codex_env(
        auth_mode="local",
        api_key=None,
        api_base_url=None,
    )

    assert temp_home is not None
    try:
        assert env["CODEX_HOME"] == str(temp_home)
        assert temp_home != codex_home
        assert (temp_home / "auth.json").read_text(
            encoding="utf-8"
        ) == '{"token":"local"}'
        assert (temp_home / "config.toml").read_text(
            encoding="utf-8"
        ) == 'model = "local"\n'
        assert (temp_home / "rules" / "default.rules").read_text(
            encoding="utf-8"
        ) == "allow\n"
        assert "CODEX_API_KEY" not in env
        assert "OPENAI_API_KEY" not in env
        assert "LLM_API_KEY" not in env
    finally:
        shutil.rmtree(temp_home, ignore_errors=True)
