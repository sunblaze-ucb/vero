from vero.curation.cli import _redact_local_codex_credentials
from vero.curation.config import CurationConfig


def _config(**overrides: object) -> CurationConfig:
    data = {
        "source_dir": "/tmp/source",
        "output_dir": "/tmp/out",
        "agent_kind": "codex",
        "codex_auth_mode": "local",
        "api_key": "secret",
        "api_base_url": "https://proxy.example",
    }
    data.update(overrides)
    return CurationConfig(**data)


def test_redact_local_codex_credentials() -> None:
    config = _config()

    _redact_local_codex_credentials(config)

    assert config.api_key is None
    assert config.api_base_url is None


def test_keep_api_mode_credentials() -> None:
    config = _config(codex_auth_mode="api")

    _redact_local_codex_credentials(config)

    assert config.api_key == "secret"
    assert config.api_base_url == "https://proxy.example"
