"""Per-agent env + dotfile materialization.

Agents need different credential / config plumbing:

- `claude-code` SDK reads ``ANTHROPIC_API_KEY`` / ``ANTHROPIC_BASE_URL`` from ``os.environ`` at query time (in-process).
- `codex` subprocess reads ``CODEX_API_KEY`` / ``OPENAI_API_KEY`` from its environ and ``CODEX_HOME/config.toml`` from disk.

``.env`` at the repo root now holds only litellm-compatible creds (``LLM_API_KEY`` / ``LLM_API_BASE`` / ``LLM_MODEL_FALLBACK``). Each ``conf/agent/<kind>.yaml`` declares *which* agent-specific env vars the shim should fill from those generic creds via an ``env:`` dict (OmegaConf interpolations do the lookup). When the agent is launched, :class:`AgentEnvShim` materializes the declared dotfiles under ``<sandbox>/.agent/<kind>/`` and returns an env dict scoped to that agent run — no global ``os.environ`` pollution for subprocess agents; a context manager for in-process agents.

Today's concrete coverage: ``claude`` + ``codex``. ``gemini`` + ``gauss`` keep their existing env plumbing until the shim is validated on the first two.
"""

from __future__ import annotations

import contextlib
import json
import os
from collections.abc import Iterator, Mapping
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

from loguru import logger
from omegaconf import OmegaConf


@dataclass
class AgentEnvShim:
    """Per-agent credential + dotfile translator.

    :param kind: agent kind (``claude`` / ``codex`` / ...).
    :param sandbox_dir: agent sandbox dir (``agent_runs/<name>/source``).
    :param env_declared: extra env vars to apply when the agent launches. Values are already-resolved strings; OmegaConf interpolations from ``conf/agent/<kind>.yaml`` run before we see them.
    :param dotfiles: list of ``{target: <rel-path>, content: <str>}``. ``target`` is relative to ``<sandbox>/.agent/<kind>/``.
    :param config_files: list of ``{target, content_type, content}`` describing per-agent CLI config files (``settings.json`` for claude, ``config.toml`` for codex). Materialized under ``<sandbox>/.<kind>/`` so the bundled CLI can be pointed at it via ``CLAUDE_CONFIG_DIR`` / ``CODEX_HOME``. Empty list = no scoping (CLI reads the user's global config dir).
    """

    kind: str
    sandbox_dir: Path
    env_declared: Mapping[str, str] = field(default_factory=dict)
    dotfiles: list[dict[str, Any]] = field(default_factory=list)
    config_files: list[dict[str, Any]] = field(default_factory=list)

    @property
    def dotdir(self) -> Path:
        return self.sandbox_dir / ".agent" / self.kind

    def materialize(self) -> Path:
        """Write dotfiles to disk. Idempotent — re-runs overwrite."""
        self.dotdir.mkdir(parents=True, exist_ok=True)
        for spec in self.dotfiles:
            target = spec.get("target")
            content = spec.get("content", "")
            if not target:
                continue
            path = self.dotdir / target
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(content, encoding="utf-8")
        return self.dotdir

    def materialize_config_dir(self) -> Path | None:
        """Materialize per-agent CLI config dir under ``<sandbox>/.<kind>/``.

        Returns the dir path when at least one file was written, ``None``
        when no ``config_files`` were declared (which signals "use the
        user's global config dir, don't touch CLAUDE_CONFIG_DIR /
        CODEX_HOME"). Each entry is ``{target, content_type, content}``
        where ``content_type`` is one of:

        - ``json`` — content is a dict, serialized via ``json.dumps``
          (indent=2 for human-readability).
        - ``toml_raw`` — content is a verbatim string. The shim does no
          parsing (avoids a tomli-w dep). Build the string in the yaml or
          via callers.
        - ``text`` — content is a verbatim string, written as-is.

        Existing dir contents are preserved; per-spec files are
        overwritten.
        """
        if not self.config_files:
            return None
        config_dir = self.sandbox_dir / f".{self.kind}"
        config_dir.mkdir(parents=True, exist_ok=True)
        for spec in self.config_files:
            target = spec.get("target")
            ctype = spec.get("content_type", "text")
            content = spec.get("content", "")
            if not target:
                continue
            path = config_dir / target
            path.parent.mkdir(parents=True, exist_ok=True)
            if ctype == "json":
                payload = json.dumps(content, indent=2)
            elif ctype == "toml_raw":
                payload = str(content)
            else:
                payload = str(content)
            path.write_text(payload, encoding="utf-8")
        return config_dir

    def build_env(self, base: Mapping[str, str] | None = None) -> dict[str, str]:
        """Return a new env dict that includes the declared overrides.

        ``base`` defaults to ``os.environ`` (copy, not reference). The result is safe to pass as ``subprocess.Popen(env=...)`` — nothing in the current process is mutated.
        """
        env = dict(base) if base is not None else dict(os.environ)
        for k, v in self.env_declared.items():
            if v is None or v == "":
                continue
            env[str(k)] = str(v)
        return env

    @contextlib.contextmanager
    def scoped_environ(self) -> Iterator[dict[str, str]]:
        """Context manager for in-process agents (e.g., ``claude-code`` SDK).

        Sets ``self.env_declared`` values on ``os.environ`` and restores the prior state on exit, including un-setting keys that weren't there before.
        """
        previous: dict[str, str | None] = {}
        for k, v in self.env_declared.items():
            if v is None or v == "":
                continue
            previous[str(k)] = os.environ.get(str(k))
            os.environ[str(k)] = str(v)
        try:
            yield dict(os.environ)
        finally:
            for k, prior in previous.items():
                if prior is None:
                    os.environ.pop(k, None)
                else:
                    os.environ[k] = prior


def shim_from_config(
    kind: str, sandbox_dir: Path, agent_cfg: Mapping[str, Any]
) -> AgentEnvShim:
    """Build a shim from a resolved agent hydra config section.

    Reads ``agent_cfg.env`` (dict, optional) + ``agent_cfg.dotfiles`` (list, optional).
    Values in ``env`` are already-resolved strings (OmegaConf has run interpolation).
    """
    env_cfg = agent_cfg.get("env") or {}
    dotfiles_cfg = agent_cfg.get("dotfiles") or []
    config_files_cfg = agent_cfg.get("config_files") or []
    # Coerce OmegaConf containers → plain dicts/lists for predictable iteration.
    env_plain = {
        str(k): ("" if v is None else str(v)) for k, v in dict(env_cfg).items()
    }
    dotfiles_plain: list[dict[str, Any]] = []
    for entry in list(dotfiles_cfg):
        d = dict(entry)
        if "target" in d:
            dotfiles_plain.append(d)
    config_files_plain: list[dict[str, Any]] = []
    for entry in list(config_files_cfg):
        # config_files entries can carry nested dicts (json content), so use
        # OmegaConf.to_container with resolve=True when the entry is still a
        # DictConfig — preserves nested structure rather than stringifying.
        if OmegaConf.is_config(entry):
            d = OmegaConf.to_container(entry, resolve=True)
        else:
            d = dict(entry)
        if isinstance(d, dict) and "target" in d:
            config_files_plain.append(d)
    shim = AgentEnvShim(
        kind=kind,
        sandbox_dir=Path(sandbox_dir),
        env_declared=env_plain,
        dotfiles=dotfiles_plain,
        config_files=config_files_plain,
    )
    _warn_on_credential_holes(env_plain, config_files_plain)
    return shim


# Auth keys we recognise as required for known providers. When a config
# declares one of these but its resolved value is empty, the agent will
# fail at runtime with an opaque 401 (or worse, succeed against the
# wrong endpoint with a leaked key from a different env var). Surface
# the hole loudly at shim-build time so the user gets a clear pointer.
_REQUIRED_AUTH_KEYS: tuple[str, ...] = (
    "OPENROUTER_API_KEY",
    "ANTHROPIC_AUTH_TOKEN",
    "ANTHROPIC_API_KEY",
    "OPENAI_API_KEY",
    "CODEX_API_KEY",
    "CODEX_AGENT_API_KEY",
)


def _warn_on_credential_holes(
    env_declared: Mapping[str, str], config_files: list[dict[str, Any]]
) -> None:
    """Loud warning when a declared auth env var resolved to empty.

    OmegaConf's ``${oc.env:VAR,DEFAULT}`` interpolation silently
    substitutes ``DEFAULT`` (often ``""`` from a credentials yaml's
    fallback chain) when ``VAR`` isn't set. The shim's ``build_env``
    further drops empty values, which means the codex / claude
    subprocess inherits the parent shell's value — usually nothing —
    and the call fails with a 401 that's hard to attribute. We catch
    the case here by walking both the env block and any config_files
    settings.json env block, and warn on every recognised auth key
    whose value resolved empty.
    """
    holes: list[str] = []
    for k in _REQUIRED_AUTH_KEYS:
        v = env_declared.get(k)
        if v is not None and v == "":
            holes.append(f"env.{k}")
    for spec in config_files:
        if spec.get("target") != "settings.json":
            continue
        content = spec.get("content")
        if not isinstance(content, dict):
            continue
        env_block = content.get("env")
        if not isinstance(env_block, dict):
            continue
        for k, v in env_block.items():
            if k in _REQUIRED_AUTH_KEYS and v == "":
                holes.append(f"settings.json/env.{k}")
    if holes:
        logger.warning(
            "credential hole(s) — these declared auth env keys resolved to "
            "empty strings: {}. The agent will see no credential for them; "
            "the bundled CLI will likely raise a 401. Set the required env "
            "var(s) in your shell or .env before launching.",
            ", ".join(sorted(set(holes))),
        )
