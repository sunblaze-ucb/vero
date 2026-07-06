"""SPEC_WRITE stage — two-substep agent loop for Python / new-source workflows.

The stage runs in one of two substeps depending on whether
``curation/spec_plan.md`` exists and is human-approved:

1. **reason** (first run, or when ``spec_plan.md`` is absent): the agent reads
   the translated ``Impl/*.lean`` files + ``manifest.json`` and writes
   ``curation/spec_plan.md`` proposing specs that cover every public API,
   including cross-API interactions. Each API must appear in ≥1 spec. The
   stage pauses for human review.

2. **formalize** (re-run after human approves the plan by adding a
   ``# APPROVED`` marker as the first non-blank line of ``spec_plan.md``):
   the agent writes ``Spec/<Module>.lean`` bodies in the canonical
   ``def spec_<name> (impl : RepoImpl) : Prop := …`` shape, threads each
   spec through the bundle, and updates ``manifest.json`` ``specs[]`` lists.
   The stage validates each spec is well-typed (`spec_shape` rule check)
   and re-runs ``lake build``.

Skill: ``vero-spec-write`` (loaded via the Skill tool).
"""

from __future__ import annotations

import json
import re
from pathlib import Path

import anyio

from vero.curation.lean_project import to_project_name
from vero.curation.stages._skill_preamble import skill_preamble
from vero.curation.stages.base import (
    StageContext,
    StageResult,
    StageRunner,
    compose_prompt,
)

_BUILD_TIMEOUT_SECONDS = 300
_APPROVAL_RE = re.compile(r"^\s*#\s*APPROVED\b", re.MULTILINE)


def is_plan_approved(plan_path: Path) -> bool:
    """Return True if the plan exists and starts with a `# APPROVED` marker."""
    if not plan_path.exists():
        return False
    text = plan_path.read_text(encoding="utf-8")
    # Approval must be near the top so a stale `# APPROVED` deep in a comment
    # block can't accidentally release the gate.
    head = "\n".join(text.splitlines()[:5])
    return bool(_APPROVAL_RE.search(head))


def determine_substep(plan_path: Path) -> str:
    """`reason` if the plan needs writing/re-writing; `formalize` once approved."""
    return "formalize" if is_plan_approved(plan_path) else "reason"


def _load_manifest_summary(project_dir: Path) -> dict:
    """Compact manifest digest for the agent prompt."""
    manifest_path = project_dir / "manifest.json"
    if not manifest_path.exists():
        return {"error": f"manifest.json missing at {manifest_path}"}
    try:
        manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as e:
        return {"error": f"manifest.json invalid: {e}"}
    out: dict = {"benchmark_id": manifest.get("benchmark_id"), "modules": []}
    for pkg in manifest.get("packages", []):
        for mod in pkg.get("modules", []):
            apis = [a.get("name") for a in mod.get("apis", []) if a.get("name")]
            specs = mod.get("specs", [])
            spec_names = [s if isinstance(s, str) else s.get("name", "") for s in specs]
            out["modules"].append(
                {
                    "name": mod.get("name"),
                    "package": pkg.get("name"),
                    "apis": apis,
                    "existing_specs": spec_names,
                }
            )
    return out


class SpecWriteStage(StageRunner):
    """Agent-driven two-substep spec authoring.

    See module docstring for the substep semantics.
    """

    name = "spec_write"
    human_review = True

    def _plan_path(self, ctx: StageContext) -> Path:
        return ctx.curation_dir / "spec_plan.md"

    def _project_dir(self, ctx: StageContext) -> Path:
        project_name = to_project_name(ctx.config.benchmark_id)
        return ctx.lean_output_dir / project_name

    def _build_reason_prompt(
        self, ctx: StageContext, project_dir: Path, plan_path: Path
    ) -> str:
        manifest_summary = _load_manifest_summary(project_dir)
        manifest_json = json.dumps(manifest_summary, indent=2)
        body = [
            "## Substep 1 of 2 — REASON about specs",
            "",
            "You are designing the formal specifications for a translated Python (or",
            "new-source) project. Read the translated `Impl/*.lean` files and the",
            f"manifest at `{project_dir}/manifest.json`, then write a proposal to",
            f"`{plan_path}`.",
            "",
            "## What goes in `spec_plan.md`",
            "",
            "For each module + each public API, propose at least one specification.",
            "**Every API must appear in ≥1 proposed spec.** Be creative: look for",
            "cross-API invariants too (e.g. `f` and `g` commute; `f` is the inverse",
            "of `g` on its image; iterating `f` preserves a measure).",
            "",
            "Output format (markdown), one section per spec:",
            "",
            "```markdown",
            "## spec_<descriptive_name>",
            "",
            "- **Module:** `<ModuleName>`",
            "- **Covers APIs:** `f`, `g` (list every API the spec mentions)",
            "- **Intent (NL):** one paragraph in plain English.",
            "- **Lean sketch:**",
            "  ```lean",
            "  def spec_<name> (impl : RepoImpl) : Prop :=",
            "    ∀ … , …  -- pseudocode is fine; substep 2 will formalize",
            "  ```",
            "- **Notes for human:** assumptions, edge cases, alternatives.",
            "```",
            "",
            "If a spec needs an existing curator-given spec helper, name it; if it",
            "needs a new one, propose it as a top-level item under",
            "`## spec_helpers (proposed)`.",
            "",
            "## Coverage check",
            "",
            "After writing the spec sections, append a coverage table:",
            "",
            "```markdown",
            "## Coverage",
            "",
            "| Module | API | Specs |",
            "|---|---|---|",
            "| Account | createAccount | spec_create_zero_balance, spec_create_exists |",
            "```",
            "",
            "## Human review",
            "",
            f"This stage will pause after `{plan_path}` is written. The human",
            "edits the plan and adds `# APPROVED` as the first non-blank line",
            "to release the gate. Re-running this stage then triggers substep 2",
            "(formalize), which writes the Lean spec defs.",
            "",
            "## Manifest digest (read-only — for your reference)",
            "",
            "```json",
            manifest_json,
            "```",
        ]
        preamble = skill_preamble("spec_write")
        return compose_prompt(
            preamble,
            body,
            ctx,
            guidance_header="## Human Guidance",
        )

    def _build_formalize_prompt(
        self, ctx: StageContext, project_dir: Path, plan_path: Path
    ) -> str:
        plan_text = plan_path.read_text(encoding="utf-8")
        body = [
            "## Substep 2 of 2 — FORMALIZE the approved plan",
            "",
            f"The human approved the spec plan at `{plan_path}` (the file starts",
            "with `# APPROVED`). Translate every `## spec_<name>` section into a",
            "`def spec_<name> (impl : RepoImpl) : Prop := …` definition in the",
            f"appropriate `{project_dir}/<Project>/Spec/<Module>.lean` file.",
            "",
            "## Hard rules (these are validator-enforced)",
            "",
            "- Every spec is `def spec_<name> (impl : RepoImpl) : Prop := …`.",
            "  The parameter name may be `_impl` if unused.",
            "- Spec files contain ONLY `def spec_*` and `def spec_helper_*`",
            "  declarations. No `theorem` / `lemma` / `example` / markers.",
            "- Spec bodies access APIs via `impl.<repo_impl_field>.<fn>`",
            "  (look at `<Project>/Bundle.lean` for the field name).",
            "- Update `manifest.json::packages[].modules[].specs[]` to list every",
            "  new spec by name (use the bare string form, kind defaults to spec).",
            "- For helpers used by specs, add to `spec_helpers[]`.",
            "",
            "## Verify before declaring done",
            "",
            f"1. `cd {project_dir} && lake build` — must succeed.",
            "2. Each module's `Spec/*.lean` file has at least one spec for every",
            "   listed API in that module's manifest entry.",
            "",
            "## Approved plan (verbatim)",
            "",
            "```markdown",
            plan_text,
            "```",
        ]
        preamble = skill_preamble("spec_write")
        return compose_prompt(
            preamble,
            body,
            ctx,
            guidance_header="## Human Guidance",
        )

    async def _run_substep_reason(
        self, ctx: StageContext, project_dir: Path, plan_path: Path
    ) -> StageResult:
        from vero.curation.agent import call_agent

        prompt = self._build_reason_prompt(ctx, project_dir, plan_path)
        _, session_id = await call_agent(
            model=ctx.config.model,
            permission_mode=ctx.config.permission_mode,
            prompt=prompt,
            tools=["Read", "Write", "Edit", "Bash", "Grep", "Glob"],
            max_turns=getattr(
                ctx.config, "max_turns_spec_write", ctx.config.max_turns_translate
            ),
            resume_session_id=ctx.resume_session_id,
            api_key=ctx.config.api_key,
            api_base_url=ctx.config.api_base_url,
            **ctx.config.agent_kwargs,
        )
        wrote_plan = plan_path.exists()
        instructions = (
            f"Substep 1 of 2 (REASON) complete.\n"
            f"Review {plan_path}\n"
            "Edit the proposed specs as needed, then add `# APPROVED` as the\n"
            "first non-blank line and re-run this stage to trigger substep 2\n"
            "(FORMALIZE).\n"
            f"  python -m vero.curation run ... --stage spec_write --force"
        )
        if not wrote_plan:
            return StageResult(
                stage=self.name,
                success=False,
                error=f"agent did not write {plan_path}",
                session_id=session_id or "",
            )
        return StageResult(
            stage=self.name,
            success=True,
            output_files=[str(plan_path)],
            human_review_required=True,
            human_review_instructions=instructions,
            session_id=session_id or "",
        )

    async def _run_substep_formalize(
        self, ctx: StageContext, project_dir: Path, plan_path: Path
    ) -> StageResult:
        from vero.curation.agent import call_agent

        prompt = self._build_formalize_prompt(ctx, project_dir, plan_path)
        _, session_id = await call_agent(
            model=ctx.config.model,
            permission_mode=ctx.config.permission_mode,
            prompt=prompt,
            tools=["Read", "Write", "Edit", "Bash", "Grep", "Glob"],
            max_turns=getattr(
                ctx.config, "max_turns_spec_write", ctx.config.max_turns_translate
            ),
            resume_session_id=ctx.resume_session_id,
            api_key=ctx.config.api_key,
            api_base_url=ctx.config.api_base_url,
            **ctx.config.agent_kwargs,
        )
        build_ok, build_output = await _run_lake_build(project_dir)
        spec_dir = project_dir / to_project_name(ctx.config.benchmark_id) / "Spec"
        spec_files = (
            sorted(str(p) for p in spec_dir.rglob("*.lean"))
            if spec_dir.exists()
            else []
        )
        if not build_ok:
            return StageResult(
                stage=self.name,
                success=False,
                error=f"lake build failed after formalize:\n{build_output[-1000:]}",
                output_files=spec_files,
                session_id=session_id or "",
            )
        return StageResult(
            stage=self.name,
            success=True,
            output_files=spec_files + [str(plan_path)],
            human_review_required=False,
            session_id=session_id or "",
        )

    async def run(self, ctx: StageContext) -> StageResult:
        project_dir = self._project_dir(ctx)
        if not project_dir.exists():
            return StageResult(
                stage=self.name,
                success=False,
                error=f"Lean project not found at {project_dir}. Run translate first.",
            )
        plan_path = self._plan_path(ctx)
        substep = determine_substep(plan_path)
        if substep == "reason":
            return await self._run_substep_reason(ctx, project_dir, plan_path)
        return await self._run_substep_formalize(ctx, project_dir, plan_path)


async def _run_lake_build(project_dir: Path) -> tuple[bool, str]:
    try:
        with anyio.fail_after(_BUILD_TIMEOUT_SECONDS):
            proc = await anyio.run_process(
                ["lake", "build"],
                cwd=project_dir,
                check=False,
            )
    except TimeoutError:
        return False, f"lake build timed out after {_BUILD_TIMEOUT_SECONDS}s"
    stdout = proc.stdout.decode("utf-8", errors="replace") if proc.stdout else ""
    stderr = proc.stderr.decode("utf-8", errors="replace") if proc.stderr else ""
    return proc.returncode == 0, stderr or stdout
