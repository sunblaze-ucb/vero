"""Base classes for pipeline stages."""

from __future__ import annotations

from abc import ABC, abstractmethod
from dataclasses import dataclass
from pathlib import Path
from typing import Optional

from pydantic import BaseModel

from vero.curation.config import CurationConfig


class StageResult(BaseModel):
    """Result of running a pipeline stage."""

    stage: str
    success: bool
    output_files: list[str] = []
    human_review_required: bool = False
    human_review_instructions: str = ""
    error: str = ""
    session_id: str = ""
    review_version: int = 0


@dataclass
class StageContext:
    """Runtime context passed to each stage's run() method."""

    config: CurationConfig
    curation_dir: Path
    source_dir: Path
    repo_root: Path
    lean_output_dir: Path
    resume_session_id: Optional[str] = None

    @classmethod
    def from_config(
        cls,
        config: CurationConfig,
        resume_session_id: Optional[str] = None,
    ) -> StageContext:
        return cls(
            config=config,
            curation_dir=config.curation_dir,
            source_dir=config.effective_source_dir,
            repo_root=config.repo_root,
            lean_output_dir=config.lean_output_dir,
            resume_session_id=resume_session_id,
        )

    def read_human_guidance(self) -> Optional[str]:
        path = self.curation_dir / "human_guidance.md"
        if path.exists():
            return path.read_text(encoding="utf-8")
        return None


class StageRunner(ABC):
    """Base class for all stage implementations.

    Subclasses set class-level `name` and `human_review` attributes,
    and implement `run(ctx)`.
    """

    name: str = ""
    human_review: bool = True

    @abstractmethod
    async def run(self, ctx: StageContext) -> StageResult: ...


def compose_prompt(
    preamble: str,
    body_parts: list[str],
    ctx: StageContext,
    *,
    guidance_header: str = "## Human Guidance",
    trailing: list[str] | None = None,
) -> str:
    """Assemble a stage prompt from its common sections.

    Structure: ``preamble → ## Task → body_parts → optional guidance → trailing``.
    The guidance section is included only if ``human_guidance.md`` exists.
    """
    parts = [preamble, "", "## Task", "", *body_parts]
    guidance = ctx.read_human_guidance()
    if guidance:
        parts.extend(["", guidance_header, guidance])
    if trailing:
        parts.extend(trailing)
    return "\n".join(parts)
