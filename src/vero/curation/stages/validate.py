"""VALIDATE stage — run validation checks on the translated benchmark.

The stage always runs deterministic rule checks. It can also run opt-in
LLM-review checks and emit human-reviewable memory candidates.
"""

from __future__ import annotations

import json
from pathlib import Path

from vero.curation.lean_project import to_project_name
from vero.curation.stages.base import StageContext, StageResult, StageRunner
from vero.curation.validation import (
    ValidationReport,
    render_memory_update_suggestions,
    run_llm_reviews_async,
    validate_benchmark,
)
from vero.curation.validation.llm_runner import (
    CODEX_LLM_REVIEW_MODEL,
    CurationAgentLLMReviewRunner,
)

REPO_ROOT = Path(__file__).resolve().parents[4]


def find_benchmark_root(
    lean_output_dir: Path, expected_project_name: str | None = None
) -> Path | None:
    """Return the directory containing ``manifest.json`` under ``lean_output_dir``.

    Searches one level deep: ``lean_output/<Project>/manifest.json``. Falls back
    to ``lean_output/manifest.json`` when the caller already points there. When
    an expected project name is available, it is authoritative; this prevents a
    stale sibling project from being selected alphabetically.
    """
    if not lean_output_dir.exists():
        return None
    if (lean_output_dir / "manifest.json").exists():
        if expected_project_name and lean_output_dir.name != expected_project_name:
            return None
        return lean_output_dir
    if expected_project_name:
        expected = lean_output_dir / expected_project_name
        if expected.is_dir() and (expected / "manifest.json").exists():
            return expected
        return None
    candidates = [
        sub
        for sub in sorted(lean_output_dir.iterdir())
        if sub.is_dir() and (sub / "manifest.json").exists()
    ]
    if len(candidates) == 1:
        return candidates[0]
    if len(candidates) > 1:
        return None
    return None


def render_report_md(report: ValidationReport) -> str:
    """Format a ValidationReport as human-readable Markdown."""
    lines = [f"# Validation report — `{report.benchmark_path}`", ""]
    lines.append(f"**Overall:** `{report.overall.upper()}`")
    if report.blockers:
        lines.extend(["", "## Blockers", ""])
        for b in report.blockers:
            lines.append(f"- {b}")
    lines.extend(["", "## Rule checks", ""])
    for name, check in report.rule_checks.items():
        lines.append(f"### `{name}` — {check.status}")
        if not check.details:
            lines.append("- (no findings)")
        for f in check.details:
            loc = f" [`{f.location}`]" if f.location else ""
            lines.append(f"- **{f.severity}:** {f.message}{loc}")
        lines.append("")
    if report.llm_review:
        lines.extend(["", "## LLM review", ""])
        for name, check in report.llm_review.items():
            lines.append(f"### `{name}` — {check.status}")
            if not check.details:
                lines.append("- (no findings)")
            for f in check.details:
                loc = f" [`{f.location}`]" if f.location else ""
                lines.append(f"- **{f.severity}:** {f.message}{loc}")
            lines.append("")
    return "\n".join(lines) + "\n"


class ValidateStage(StageRunner):
    """Run rule-based validation on the translated benchmark tree."""

    name = "validate"
    human_review = False

    async def run(self, ctx: StageContext) -> StageResult:
        config = getattr(ctx, "config", None)
        benchmark_id = getattr(config, "benchmark_id", "") if config is not None else ""
        expected_project_name = to_project_name(benchmark_id) if benchmark_id else None
        benchmark = find_benchmark_root(ctx.lean_output_dir, expected_project_name)
        if benchmark is None:
            suffix = (
                f" matching expected project {expected_project_name!r}"
                if expected_project_name
                else ""
            )
            return StageResult(
                stage=self.name,
                success=False,
                error=(
                    f"No benchmark with manifest.json{suffix} found under "
                    f"{ctx.lean_output_dir}"
                ),
            )

        report = validate_benchmark(benchmark, skip_build=False)

        if bool(getattr(config, "validate_llm_review", False)):
            memory_setting = getattr(config, "validate_llm_review_memory_path", None)
            memory_path = Path(memory_setting) if memory_setting else None
            checks_setting = getattr(config, "validate_llm_review_checks_path", None)
            checks_path = Path(checks_setting) if checks_setting else None
            only = (
                tuple(getattr(config, "validate_llm_review_checks", []) or []) or None
            )
            runner = CurationAgentLLMReviewRunner(
                model=CODEX_LLM_REVIEW_MODEL,
                permission_mode=getattr(config, "permission_mode"),
                max_turns=getattr(config, "max_turns_validate", 10),
                api_key=getattr(config, "api_key", None),
                api_base_url=getattr(config, "api_base_url", None),
                codex_auth_mode=getattr(config, "codex_auth_mode", "api"),
                codex_sandbox_mode=getattr(
                    config, "codex_sandbox_mode", "danger-full-access"
                ),
                codex_network_access=getattr(config, "codex_network_access", False),
                codex_timeout_seconds=getattr(config, "codex_timeout_seconds", 1800),
                codex_model_reasoning_effort=getattr(
                    config, "codex_model_reasoning_effort", None
                ),
            )
            report.llm_review = await run_llm_reviews_async(
                benchmark,
                runner=runner,
                reference_path=REPO_ROOT / "reference" / "BankLedger",
                memory_path=memory_path,
                only=only,
                rule_checks=report.rule_checks,
                check_specs_path=checks_path,
            )

        ctx.curation_dir.mkdir(parents=True, exist_ok=True)
        validate_dir = ctx.curation_dir / "validate"
        validate_dir.mkdir(parents=True, exist_ok=True)

        json_path = ctx.curation_dir / "validate.json"
        json_path.write_text(
            json.dumps(report.to_dict(), indent=2) + "\n", encoding="utf-8"
        )

        md_path = validate_dir / "report.md"
        md_path.write_text(render_report_md(report), encoding="utf-8")
        output_files = [str(json_path), str(md_path)]

        if report.llm_review:
            memory_path = validate_dir / "memory_candidates.md"
            memory_path.write_text(
                render_memory_update_suggestions(
                    benchmark.name,
                    report.llm_review,
                )
                + "\n",
                encoding="utf-8",
            )
            output_files.append(str(memory_path))

        success = report.overall != "fail"
        return StageResult(
            stage=self.name,
            success=success,
            output_files=output_files,
            error="\n".join(report.blockers) if not success else "",
        )
