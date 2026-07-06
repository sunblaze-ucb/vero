"""DISCOVER stage — agent scans source and classifies all items."""

from __future__ import annotations

import json

from vero.curation.stages._skill_preamble import skill_preamble
from vero.curation.stages.base import (
    StageContext,
    StageResult,
    StageRunner,
    compose_prompt,
)


class DiscoverStage(StageRunner):
    name = "discover"
    human_review = True

    def _build_prompt(self, ctx: StageContext) -> str:
        lang = ctx.config.source_language
        source_dir = ctx.source_dir
        repo_root = ctx.repo_root
        curation_dir = ctx.curation_dir

        body: list[str] = [
            f"Scan all source files in `{source_dir}` ({lang.value} project).",
            "Before scanning, read `.vero/source_index.json` under the output workspace.",
            "Treat it as the no-LLM source-wide name registry: every entity listed there",
            "must either be confirmed, refined, or explicitly marked as a false-positive",
            "in the discovery output. Do not silently drop registry entries.",
        ]
        if str(repo_root) != str(source_dir):
            body.append(
                f"The repository root is `{repo_root}` — check the README and other docs there"
                " for project context before classifying items."
            )
        body.extend(
            [
                "",
                "For each source file, classify every top-level item and write a discovery",
                f"markdown to `{curation_dir}/discovery/`. Use the file path (with `--` replacing `/`)",
                "as the markdown filename.",
                "",
                f"Then write `{curation_dir}/api.md` with a summary table.",
                "",
                f"Finally, write `{curation_dir}/discovery_report.json` with a machine-readable",
                "DiscoveryReport containing all discovered items. Preserve `source_file`,",
                "`source_line`, signatures, and stable source ids from source_index.json when possible.",
                "Do not preserve source_index roles as semantic classifications: the source",
                "index is role-neutral inventory, so roles must be assigned from source text",
                "and discovery evidence.",
            ]
        )

        return compose_prompt(skill_preamble("discover", lang), body, ctx)

    async def run(self, ctx: StageContext) -> StageResult:
        from vero.curation.agent import call_agent

        discovery_dir = ctx.curation_dir / "discovery"
        discovery_dir.mkdir(parents=True, exist_ok=True)

        prompt = self._build_prompt(ctx)
        if ctx.resume_session_id:
            prompt = "Continue the discovery scan where you left off."

        _, session_id = await call_agent(
            model=ctx.config.model,
            permission_mode=ctx.config.permission_mode,
            prompt=prompt,
            tools=["Read", "Write", "Bash", "Grep", "Glob"],
            max_turns=ctx.config.max_turns_discover,
            resume_session_id=ctx.resume_session_id,
            api_key=ctx.config.api_key,
            api_base_url=ctx.config.api_base_url,
            **ctx.config.agent_kwargs,
        )

        output_files = []
        report_json = ctx.curation_dir / "discovery_report.json"
        api_md = ctx.curation_dir / "api.md"
        discovery_mds = list(discovery_dir.glob("*.md"))

        if report_json.exists():
            output_files.append(str(report_json))
        if api_md.exists():
            output_files.append(str(api_md))
        output_files.extend(str(f) for f in discovery_mds)

        success, error = _validate_discovery_outputs(
            ctx=ctx,
            report_json=report_json,
            api_md=api_md,
            discovery_mds=discovery_mds,
        )

        return StageResult(
            stage=self.name,
            success=success,
            output_files=output_files,
            human_review_required=True,
            human_review_instructions=(
                f"Review discovery files in {discovery_dir}/\n"
                "- Check [x] items you want translated\n"
                "- Uncheck [ ] items to exclude\n"
                "- Add notes as needed\n"
                f"Then re-run with --stage select"
            ),
            error=error,
            session_id=session_id or "",
        )


def _validate_discovery_outputs(
    *,
    ctx: StageContext,
    report_json,
    api_md,
    discovery_mds,
) -> tuple[bool, str]:
    """Check that discovery produced its required final artifacts.

    Per-file markdowns alone are not enough: later stages consume the
    machine-readable report and human reviewers consume the merged API catalog.
    The source index is a no-LLM registry, so use it to catch partial scans.
    """

    errors: list[str] = []
    if not discovery_mds:
        errors.append("no per-file discovery markdowns were produced")
    if not api_md.exists():
        errors.append(f"missing API catalog: {api_md}")
    if not report_json.exists():
        errors.append(f"missing discovery report: {report_json}")
        return False, "; ".join(errors)

    try:
        report = json.loads(report_json.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        errors.append(f"invalid discovery report JSON: {exc}")
        return False, "; ".join(errors)

    items = report.get("items")
    if not isinstance(items, list) or not items:
        errors.append("discovery report has no nonempty `items` list")

    source_index_path = ctx.config.workspace / ".vero" / "source_index.json"
    if source_index_path.exists() and isinstance(items, list):
        try:
            source_index = json.loads(source_index_path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as exc:
            errors.append(f"invalid source index JSON: {exc}")
        else:
            missing_files = _missing_source_index_file_coverage(source_index, items)
            if missing_files:
                preview = ", ".join(missing_files[:10])
                suffix = (
                    ""
                    if len(missing_files) <= 10
                    else f", ... (+{len(missing_files) - 10} more)"
                )
                errors.append(
                    "discovery report does not cover source-index files: "
                    f"{preview}{suffix}"
                )

    return not errors, "; ".join(errors)


def _missing_source_index_file_coverage(source_index: dict, items: list) -> list[str]:
    indexed_files = sorted(
        {
            str(entity.get("source_file", "")).strip()
            for entity in source_index.get("entities", [])
            if isinstance(entity, dict) and str(entity.get("source_file", "")).strip()
        }
    )
    if not indexed_files:
        return []

    reported_files = sorted(
        {
            str(item.get("source_file", "")).strip()
            for item in items
            if isinstance(item, dict) and str(item.get("source_file", "")).strip()
        }
    )
    return [
        path
        for path in indexed_files
        if not _source_file_is_reported(path, reported_files)
    ]


def _source_file_is_reported(indexed_path: str, reported_paths: list[str]) -> bool:
    """Return true if a discovery item covers a source-index file path.

    Agents may preserve source files either relative to `source_dir`
    (`AuxLib.v`) or relative to the repo root (`theories/AuxLib.v`). Treat a
    suffix match across path boundaries as the same source file.
    """

    indexed = indexed_path.strip("/")
    for raw_reported in reported_paths:
        reported = raw_reported.strip("/")
        if reported == indexed:
            return True
        if reported.endswith(f"/{indexed}") or indexed.endswith(f"/{reported}"):
            return True
    return False
