"""Configuration for the curation pipeline."""

from __future__ import annotations

from pathlib import Path
from typing import Optional

import yaml
from pydantic import BaseModel

from vero.curation.models import SourceLanguage


class StageStatus(BaseModel):
    """Tracks the state of a single pipeline stage."""

    status: str = "pending"  # pending | in_progress | completed | failed
    completed_at: str = ""
    session_id: str = ""
    review_version: int = 0
    error: str = ""


class CurationConfig(BaseModel):
    """Pipeline configuration, serialized as config.yaml in the workspace."""

    source_dir: str
    source_subdir: str = ""
    output_dir: str
    source_language: Optional[SourceLanguage] = None
    benchmark_id: str = ""
    workflow: str = "verified_to_lean"
    agent_kind: str = "claude"
    model: str = "claude-sonnet-4-6"
    max_turns_discover: int = 50
    max_turns_select: int = 30
    max_turns_plan: int = 30
    max_turns_translate: int = 100
    max_turns_python_adjust: int = 100
    max_turns_python_curate: int = 200
    max_turns_spec_write: int = 50
    max_turns_orchestrator: int = 200
    max_turns_per_module: int = 40
    max_turns_validate: int = 10
    max_concurrent_executors: int = 4
    max_executor_retries: int = 2
    use_orchestrator: bool = True
    lean_version: str = "4.29.1"
    permission_mode: str = "acceptEdits"

    # Optional: use an external API (e.g. LiteLLM proxy) instead of OAuth
    api_key: Optional[str] = None
    api_base_url: Optional[str] = None

    # Codex backend options. ``codex_auth_mode=local`` uses the user's normal
    # local Codex login/subscription and intentionally ignores API key fields.
    codex_auth_mode: str = "api"  # api | local
    codex_sandbox_mode: str = "danger-full-access"
    codex_timeout_seconds: int = 1800
    codex_network_access: bool = False
    codex_model_reasoning_effort: Optional[str] = None  # low | medium | high | xhigh
    validate_llm_review: bool = False
    validate_llm_review_checks: list[str] = []
    validate_llm_review_memory_path: Optional[str] = None
    validate_llm_review_checks_path: Optional[str] = None

    # Lean MCP tools: set to False to disable lean-lsp-mcp and lean-explore
    enable_lean_mcp: bool = True

    # Filled during INIT
    repo_url: str = ""
    commit_hash: str = ""

    # Stage tracking (replaces .stage_*.json files)
    stages: dict[str, StageStatus] = {}

    @property
    def effective_source_dir(self) -> Path:
        base = Path(self.source_dir)
        if self.source_subdir:
            return base / self.source_subdir
        return base

    @property
    def repo_root(self) -> Path:
        return Path(self.source_dir)

    @property
    def workspace(self) -> Path:
        return Path(self.output_dir)

    @property
    def curation_dir(self) -> Path:
        return self.workspace / "curation"

    @property
    def lean_output_dir(self) -> Path:
        return self.workspace / "lean_output"

    @property
    def agent_kwargs(self) -> dict[str, object]:
        return {
            "agent_kind": self.agent_kind,
            "codex_auth_mode": self.codex_auth_mode,
            "codex_sandbox_mode": self.codex_sandbox_mode,
            "codex_timeout_seconds": self.codex_timeout_seconds,
            "codex_network_access": self.codex_network_access,
            "codex_model_reasoning_effort": self.codex_model_reasoning_effort,
        }

    def get_stage_status(self, name: str) -> StageStatus:
        return self.stages.get(name, StageStatus())

    def set_stage_status(self, name: str, **kwargs: object) -> None:
        if name not in self.stages:
            self.stages[name] = StageStatus()
        for k, v in kwargs.items():
            setattr(self.stages[name], k, v)

    def save(self, path: Optional[Path] = None) -> Path:
        out = path or (self.workspace / "config.yaml")
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(
            yaml.dump(self.model_dump(mode="json"), default_flow_style=False),
            encoding="utf-8",
        )
        return out

    @classmethod
    def load(cls, path: Path) -> CurationConfig:
        data = yaml.safe_load(path.read_text(encoding="utf-8"))
        return cls(**data)
