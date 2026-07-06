"""Orchestrated TRANSLATE stage — uses orchestrator-executor architecture.

Drop-in replacement for ``TranslateStage`` that decomposes translation
into per-module tasks via an orchestrator agent. Falls back to the
original monolithic agent when ``use_orchestrator=False``.
"""

from __future__ import annotations

from vero.curation.lean_project import to_project_name
from vero.curation.stages.base import StageContext, StageResult, StageRunner
from vero.curation.stages.translate import TranslateStage


class OrchestratedTranslateStage(StageRunner):
    """Translate stage with orchestrator-executor architecture."""

    name = "translate"
    human_review = True

    def _project_dir(self, ctx: StageContext):
        project_name = to_project_name(ctx.config.benchmark_id)
        return ctx.lean_output_dir / project_name

    async def run(self, ctx: StageContext) -> StageResult:
        if not ctx.config.use_orchestrator:
            # Fall back to original single-agent translate
            return await TranslateStage().run(ctx)

        from vero.curation.marker import (
            count_metrics,
            extract_tasks_from_project,
            validate_markers,
        )
        from vero.curation.orchestrator.orchestrator import (
            TranslationOrchestrator,
        )
        from vero.curation.stages.translate import (
            _render_review_markdown,
            _run_lake_build,
        )

        project_dir = self._project_dir(ctx)

        # Run orchestrator
        orchestrator = TranslationOrchestrator(
            ctx=ctx,
            project_dir=project_dir,
            max_concurrent=ctx.config.max_concurrent_executors,
            max_retries=ctx.config.max_executor_retries,
        )
        state = await orchestrator.run()

        # Post-process: same as original translate stage
        output_files = [str(project_dir)]
        project_name = to_project_name(ctx.config.benchmark_id)

        build_ok, build_output = await _run_lake_build(project_dir)

        all_errors: list[str] = []
        if not build_ok:
            all_errors.append(f"lake build failed:\n{build_output.strip()}")
        for lean_file in project_dir.rglob("*.lean"):
            content = lean_file.read_text(encoding="utf-8")
            errors = validate_markers(content)
            for e in errors:
                rel = lean_file.relative_to(project_dir)
                all_errors.append(f"{rel}: {e}")

        metrics = count_metrics(project_dir)
        tasks = extract_tasks_from_project(project_dir)

        manifest_path = project_dir / "manifest.json"
        if manifest_path.exists():
            output_files.append(str(manifest_path))

        review_md = _render_review_markdown(
            project_dir,
            project_name,
            build_ok,
            build_output,
            metrics,
            all_errors,
            tasks,
        )
        review_path = ctx.curation_dir / "review.md"
        review_path.write_text(review_md, encoding="utf-8")
        output_files.append(str(review_path))

        # Add orchestrator summary to review
        orch_summary = (
            f"\n## Orchestrator Summary\n\n"
            f"- Modules completed: {len(state.completed)}/{len(state.units)}\n"
            f"- Modules failed: {len(state.failed)}\n"
            f"- Layers: {state.total_layers}\n"
        )
        if state.failed:
            orch_summary += "\nFailed modules:\n"
            for name, result in state.failed.items():
                orch_summary += f"- {name}: {result.error or result.marker_errors}\n"

        with open(review_path, "a", encoding="utf-8") as f:
            f.write(orch_summary)

        success = len(all_errors) == 0

        return StageResult(
            stage=self.name,
            success=success,
            output_files=output_files,
            human_review_required=True,
            human_review_instructions=(
                f"Review the Lean project at {project_dir}\n"
                f"Review metrics in {review_path}\n"
                f"Orchestrator state at {ctx.config.workspace}/curation/orchestrator_state.json\n"
                "Add `-- !curation @human: feedback` comments in Lean files as needed.\n"
                "Re-run with --stage translate --force to re-translate.\n"
                "When happy, --stage validate runs rule-based + optional LLM checks."
            ),
            review_version=1,
        )
