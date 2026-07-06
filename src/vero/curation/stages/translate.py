"""TRANSLATE stage — agent emits the Lean project per the ratified paradigm.

The agent loads the ``vero-translate`` skill (which cites
``reference/BankLedger/`` as the canonical shape) and the matching
``vero-source-<lang>`` skill. It translates the items listed in
``.vero/plan.json`` into Impl/ + Spec/ + Bundle.lean + Harness.lean
+ Test.lean, wraps each ``sorry`` stub in the correct ``!benchmark``
marker, and populates ``manifest.json.packages[]`` in place.

``Proof/`` is NOT emitted here — it is materialized downstream at
pre-agent-gen.
"""

from __future__ import annotations

from pathlib import Path
from typing import Iterable

import anyio

from vero.curation.feedback import (
    extract_lean_feedback,
    format_lean_feedback_for_prompt,
)
from vero.curation.lean_project import to_project_name
from vero.curation.marker import (
    count_metrics,
    extract_tasks_from_project,
    validate_markers,
)
from vero.curation.models import TaskEntry
from vero.curation.stages._skill_preamble import skill_preamble
from vero.curation.stages.base import (
    StageContext,
    StageResult,
    StageRunner,
    compose_prompt,
)

_BUILD_TIMEOUT_SECONDS = 300


def _render_review_markdown(
    project_dir: Path,
    project_name: str,
    build_ok: bool,
    build_output: str,
    metrics: dict,
    all_errors: Iterable[str],
    tasks: list[TaskEntry],
) -> str:
    """Render the translation-review markdown shown to the human reviewer."""
    build_status = "PASS" if build_ok else "FAIL"
    lines = [
        "# Translation Review\n",
        f"## Build Status: {build_status}\n",
        f"Command: `cd {project_dir} && lake build`\n",
    ]
    if not build_ok:
        lines.append(f"```\n{build_output.strip()}\n```\n")

    lines.append("## Metrics\n")
    for k, v in metrics.items():
        lines.append(f"- **{k}:** {v}")
    lines.append("")

    errors = list(all_errors)
    if errors:
        lines.append("## Errors\n")
        for e in errors:
            lines.append(f"- {e}")
        lines.append("")

    lines.append(f"## Benchmark Tasks ({len(tasks)} total)\n")
    for t in tasks:
        sorry_marker = " (sorry)" if t.is_sorry else ""
        lines.append(f"- `{t.key}` `{t.api}` in `{t.file}`:{t.line}{sorry_marker}")

    lines.extend(
        [
            "",
            "## Human Feedback",
            "",
            "Add `-- !curation @human: <note>` comments directly in the Lean",
            "files, then re-run with `--stage translate --force`.",
        ]
    )

    return "\n".join(lines) + "\n"


class TranslateStage(StageRunner):
    name = "translate"
    human_review = True

    def _build_prompt(
        self, ctx: StageContext, project_dir: Path, review_version: int
    ) -> str:
        curation_dir = ctx.curation_dir
        vero_dir = curation_dir.parent / ".vero"
        project_name = to_project_name(ctx.config.benchmark_id)
        preamble = skill_preamble("translate", ctx.config.source_language)

        if review_version == 1:
            body = [
                "Load the `vero-translate` skill. Also load the matching",
                f"`vero-source-{{{ctx.config.source_language.value}}}` skill.",
                "",
                "## Canonical shape",
                "",
                "`reference/BankLedger/` is the living contract. Read those files",
                "when uncertain about marker placement, Bundle.lean shape,",
                "Harness.lean wiring, or lakefile template.",
                "",
                "## Inputs",
                "",
                "- `.vero/plan.json` — the approved translation plan",
                "  (schema: `docs/pipeline-schema.md`).",
                f"- Source code at `{ctx.source_dir}`.",
                f"- Lean scaffold at `{project_dir}/` (created by init):",
                f"  `{project_name}.lean` root hub (empty), `lakefile.toml`,",
                "  `lean-toolchain`, `manifest.json` (empty `packages[]`).",
                "",
                "## Output shape (non-negotiable, per reference/BankLedger/)",
                "",
                f"- `{project_dir}/{project_name}.lean` — root hub (imports only).",
                f"- `{project_dir}/{project_name}/Impl/<Module>.lean` — types,",
                "  `namespace Bank`, sig abbrevs, stubs with `code`/`code_aux`",
                "  markers + `!curation @review v1` annotations.",
                f"- `{project_dir}/{project_name}/Spec/<Module>.lean` — frozen,",
                "  `def spec_*` only, NO markers. Specs use",
                "  `impl.<repo_impl_field>.<fn>` access.",
                f"- `{project_dir}/{project_name}/Bundle.lean` —",
                "  `structure <Project>Bundle where` with one field per API.",
                f"- `{project_dir}/{project_name}/Harness.lean` —",
                "  `structure RepoImpl where <pkg> : <Project>Bundle`,",
                "  `def canonical : RepoImpl := { … }`, `joint_unsat` macro.",
                f"- `{project_dir}/{project_name}/Test.lean` — `#guard`",
                "  tests against `Bank.*` directly. No markers, no `Bank.Ref`.",
                "",
                "**Fill reference implementations INSIDE `code` markers — not `sorry`.**",
                "The curator writes real working code there; pre-agent-gen replaces",
                "marker content with `sorry` before the LLM sees the benchmark.",
                "This gives one source of truth and lets `#guard`s hit the real",
                "reference at build time.",
                f"- `{project_dir}/manifest.json` — update `packages[]` to reflect",
                "  emitted files (apis with `{name, sig, type}`, specs list).",
                "",
                "**DO NOT emit `Proof/`** — it is materialized downstream.",
                "",
                "## Hard rules",
                "",
                "- Only 7 `!benchmark` keys: imports, global_aux, code,",
                "  code_aux, proof, proof_aux, claim. Retired keys",
                "  (spec, spec_aux, claim_aux, def_aux, def_body, precond*,",
                "  postcond*) are errors.",
                "- `imports` marker sits immediately after the actual",
                "  `import` lines, BEFORE the module docstring.",
                "- `proof_aux` at file level — never between `by` and the proof",
                "  body.",
                "- Spec/*.lean has no markers of any prefix.",
                "- No `Sig.lean`, no `Types.lean` — types + sigs live in Impl/*.",
                "- `lake build` must pass on the final tree.",
                "",
                f"After each layer, run `cd {project_dir} && lake build` to verify.",
                "",
                "Use `-- !curation @question <target>: <q>` to ask the human",
                "about translation decisions. These are shown in review.",
            ]
        else:
            body = [
                f"This is review round v{review_version} for `{project_dir}/`.",
                "",
                "Read the human's feedback below and address each item:",
                f"1. For each `-- !curation @review v{review_version - 1}` with feedback: apply the fix, archive the old",
                f"   comment as `-- !curation @v{review_version - 1} ... [RESOLVED]`, and write a new",
                f"   `-- !curation @review v{review_version} [x] name — applied fix` comment.",
                "2. For each `-- !curation @human:` comment: address it, then archive as",
                f"   `-- !curation @v{review_version - 1}-human: ... [NOTED]`.",
                "3. For each `-- !curation @question` you previously asked: check if the human answered",
                "   (look for `-- !curation @answer:` near it). Archive as",
                f"   `-- !curation @v{review_version - 1}-answer: ... [ANSWERED]`.",
                "",
                f"Run `cd {project_dir} && lake build` to verify after changes.",
                f"Source code is at `{ctx.source_dir}` for reference.",
                "",
                f"Plan is at `{vero_dir}/plan.json`.",
            ]

        trailing: list[str] = []
        if project_dir.exists() and review_version > 1:
            feedback = extract_lean_feedback(project_dir)
            feedback_text = format_lean_feedback_for_prompt(
                feedback, review_version - 1
            )
            if feedback_text:
                trailing = ["", feedback_text]

        return compose_prompt(
            preamble,
            body,
            ctx,
            guidance_header="## Human Guidance (from human_guidance.md)",
            trailing=trailing,
        )

    def _project_dir(self, ctx: StageContext) -> Path:
        """Init stage has already scaffolded the project; just return its path."""
        project_name = to_project_name(ctx.config.benchmark_id)
        return ctx.lean_output_dir / project_name

    async def _post_process(self, ctx: StageContext, project_dir: Path) -> StageResult:
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

        # manifest.json is populated by the agent per vero-translate guidance;
        # the validate stage will check manifest-vs-code consistency.
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

        success = len(all_errors) == 0

        return StageResult(
            stage=self.name,
            success=success,
            output_files=output_files,
            human_review_required=True,
            human_review_instructions=(
                f"Review the Lean project at {project_dir}\n"
                f"Review metrics in {review_path}\n"
                "Add `-- !curation @human: feedback` comments in Lean files as needed.\n"
                "Re-run with --stage translate --force to apply feedback.\n"
                "Re-run with --stage translate --continue if the agent ran out of turns.\n"
                "When happy, --stage validate runs rule-based + optional LLM checks."
            ),
        )

    async def run(self, ctx: StageContext) -> StageResult:
        from vero.curation.agent import build_lean_mcp_servers, call_agent

        project_dir = self._project_dir(ctx)

        prev_status = ctx.config.get_stage_status(self.name)
        prev_version = prev_status.review_version
        review_version = prev_version + 1 if not ctx.resume_session_id else prev_version

        prompt = self._build_prompt(ctx, project_dir, review_version)
        if ctx.resume_session_id:
            prompt = "Continue the translation where you left off. Check what remains to be done."

        mcp_servers = None
        if ctx.config.enable_lean_mcp:
            mcp_servers = build_lean_mcp_servers(str(project_dir))

        _, session_id = await call_agent(
            model=ctx.config.model,
            permission_mode=ctx.config.permission_mode,
            prompt=prompt,
            tools=["Read", "Write", "Edit", "Bash", "Grep", "Glob"],
            max_turns=ctx.config.max_turns_translate,
            resume_session_id=ctx.resume_session_id,
            api_key=ctx.config.api_key,
            api_base_url=ctx.config.api_base_url,
            mcp_servers=mcp_servers,
            **ctx.config.agent_kwargs,
        )

        result = await self._post_process(ctx, project_dir)
        result.session_id = session_id or ""
        result.review_version = review_version
        return result


async def _run_lake_build(project_dir: Path) -> tuple[bool, str]:
    """Run ``lake build`` (uses defaultTargets from the new lakefile form)."""
    try:
        with anyio.fail_after(_BUILD_TIMEOUT_SECONDS):
            proc = await anyio.run_process(
                ["lake", "build"],
                cwd=project_dir,
                check=False,
            )
    except TimeoutError:
        return False, (f"lake build timed out after {_BUILD_TIMEOUT_SECONDS}s")

    stdout = proc.stdout.decode("utf-8", errors="replace") if proc.stdout else ""
    stderr = proc.stderr.decode("utf-8", errors="replace") if proc.stderr else ""
    return proc.returncode == 0, stderr or stdout
