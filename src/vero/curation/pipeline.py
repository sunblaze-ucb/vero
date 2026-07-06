"""Pipeline orchestration — manages workflows and stage execution."""

from __future__ import annotations

from datetime import datetime, timezone

from loguru import logger

from vero.curation.config import CurationConfig
from vero.curation.stages.base import StageContext, StageResult, StageRunner
from vero.curation.stages.discover import DiscoverStage
from vero.curation.stages.init import InitStage
from vero.curation.stages.orchestrated_translate import OrchestratedTranslateStage
from vero.curation.stages.plan import PlanStage
from vero.curation.stages.python_adjust_bodies import PythonAdjustBodiesStage
from vero.curation.stages.python_curate import PythonCurateStage
from vero.curation.stages.python_from_json import PythonFromJsonStage
from vero.curation.stages.select import SelectStage
from vero.curation.stages.source_index import SourceIndexStage
from vero.curation.stages.spec_write import SpecWriteStage
from vero.curation.stages.validate import ValidateStage


class Pipeline:
    """Base pipeline class. Subclasses define the stage sequence."""

    stages: list[type[StageRunner]] = []

    def __init__(self, config: CurationConfig) -> None:
        self.config = config

    async def run(
        self,
        start_from: str | None = None,
        force: bool = False,
        continue_session: bool = False,
    ) -> list[StageResult]:
        """Run pipeline from start_from, pausing for human review as needed."""
        results: list[StageResult] = []
        started = start_from is None

        for stage_cls in self.stages:
            name = stage_cls.name

            if not started:
                if name == start_from:
                    started = True
                else:
                    continue

            status = self.config.get_stage_status(name)

            if not force and not continue_session and status.status == "completed":
                logger.info(f"Stage {name} already completed, skipping")
                continue

            logger.info(f"Running stage: {name}")

            resume_id = None
            if continue_session:
                resume_id = status.session_id or None
                if resume_id:
                    logger.info(f"Resuming session: {resume_id}")
                else:
                    logger.warning("No session_id found to resume, starting fresh")

            ctx = StageContext.from_config(self.config, resume_session_id=resume_id)

            self.config.set_stage_status(name, status="in_progress")
            self.config.save()

            runner = stage_cls()
            result = await runner.run(ctx)

            self.config.set_stage_status(
                name,
                status="completed" if result.success else "failed",
                completed_at=datetime.now(timezone.utc).isoformat(),
                session_id=result.session_id,
                review_version=result.review_version,
                error=result.error,
            )
            self.config.save()

            results.append(result)

            if not result.success:
                logger.error(f"Stage {name} failed: {result.error}")
                break

            if result.human_review_required:
                _print_review_instructions(name, result)
                break

        return results

    def status(self) -> dict[str, str]:
        return {
            s.name: self.config.get_stage_status(s.name).status for s in self.stages
        }


class VerifiedToLeanPipeline(Pipeline):
    """Workflow for translating verified code (Dafny/Verus/Coq) to Lean 4."""

    stages = [
        InitStage,
        SourceIndexStage,
        DiscoverStage,
        SelectStage,
        PlanStage,
        OrchestratedTranslateStage,
        ValidateStage,
    ]


class PythonSpecPipeline(Pipeline):
    """Workflow for Python repos where specs are written after translation."""

    stages = [
        InitStage,
        SourceIndexStage,
        DiscoverStage,
        SelectStage,
        PlanStage,
        OrchestratedTranslateStage,
        SpecWriteStage,
        ValidateStage,
    ]


class PythonFromBenchmarkJsonPipeline(Pipeline):
    """Workflow for Python repos pre-curated into ``benchmark.json``.

    Agent-driven mode A: one curation stage
    that takes ``benchmark.json`` as the API-selection / signature
    *reference* and ``original_python/`` as the implementation *truth*,
    and emits a complete bundle-paradigm Lean tree with real Impls — no
    ``sorry`` in code blocks. Spec files are stubs at this stage;
    ``spec_write`` runs separately later.

    1. ``PythonCurateStage`` — single-agent translation that subsumes the
       previous deterministic ``PythonFromJsonStage`` + post-hoc
       ``PythonAdjustBodiesStage`` pair. The deterministic scaffolder is
       retained as a separate pipeline / CLI subcommand for use cases
       where a fully-mechanical scaffold is preferable.

    Both ``SpecWriteStage`` and ``ValidateStage`` are intentionally absent
    from the default pipeline at this point. ``spec_write`` runs
    separately later when the user OKs spec authoring on a representative
    slice. ``validate`` is deferred too — its primary value at this stage
    is the LLM-review track, which is noisy and expensive on the bulk
    runs; the rule-based safety checks (manifest-vs-code, file-roles,
    Lake build) are partially covered by ``PythonCurateStage``'s own
    post-agent verification (lake-clean + manifest schema + spec stub
    presence) and the rest can be swept in a follow-up
    ``--stage validate`` invocation when the curate set has stabilised.

    The legacy two-phase pipeline lives at
    ``PythonFromBenchmarkJsonScaffoldPipeline`` (see below) for any user
    that explicitly needs the deterministic scaffold + adjust-bodies
    flow.
    """

    stages = [
        PythonCurateStage,
    ]


class PythonFromBenchmarkJsonScaffoldPipeline(Pipeline):
    """Legacy two-phase mode-A pipeline.

    Kept as an explicit fallback for the deterministic-scaffolder route:
    ``PythonFromJsonStage`` writes API sigs + ``sorry`` stubs from
    ``benchmark.json`` (no agent call), then
    ``PythonAdjustBodiesStage`` fills bodies by translating the Python
    source. ``SpecWriteStage`` + ``ValidateStage`` close the pipeline.
    Use the agent-driven ``PythonFromBenchmarkJsonPipeline`` by default;
    fall back to this only when the deterministic scaffold is preferred.
    """

    stages = [
        PythonFromJsonStage,
        PythonAdjustBodiesStage,
        SpecWriteStage,
        ValidateStage,
    ]


class LeanSpecPipeline(Pipeline):
    """Workflow for Lean source — extract specs from existing theorems.

    Same stage scaffolding as ``verified_to_lean``. The translate stage's
    ``vero-source-lean`` skill carries the extraction-specific guidance
    (theorems → spec defs, bundle-qualified API access, etc.).

    There is **no** ``spec_write`` step. Lean→Lean curation is honest
    extraction of what the source already proves, not synthesis of new
    specs. Adding LLM-invented specs would dilute the benchmark with
    claims the upstream repo never made; if a curator genuinely needs
    more specs they should extend the upstream first, then re-curate.
    """

    stages = [
        InitStage,
        SourceIndexStage,
        DiscoverStage,
        SelectStage,
        PlanStage,
        OrchestratedTranslateStage,
        ValidateStage,
    ]


WORKFLOWS: dict[str, type[Pipeline]] = {
    "verified_to_lean": VerifiedToLeanPipeline,
    "python_spec": PythonSpecPipeline,
    "python_from_benchmark_json": PythonFromBenchmarkJsonPipeline,
    "python_from_benchmark_json_scaffold": PythonFromBenchmarkJsonScaffoldPipeline,
    "lean_spec": LeanSpecPipeline,
}


def get_pipeline(config: CurationConfig) -> Pipeline:
    """Create a pipeline instance for the configured workflow."""
    cls = WORKFLOWS.get(config.workflow)
    if not cls:
        raise ValueError(
            f"Unknown workflow '{config.workflow}'. Available: {', '.join(WORKFLOWS)}"
        )
    return cls(config)


def _print_review_instructions(stage_name: str, result: StageResult) -> None:
    print()
    print("=" * 60)
    print(f"  STAGE {stage_name.upper()} COMPLETE — HUMAN REVIEW REQUIRED")
    print("=" * 60)
    print()
    print(result.human_review_instructions)
    print()
    print("Output files:")
    for f in result.output_files:
        print(f"  {f}")
    print()
