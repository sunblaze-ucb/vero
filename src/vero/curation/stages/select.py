"""SELECT stage — agent computes dependency closure and translation plan."""

from __future__ import annotations

from vero.curation.stages._skill_preamble import skill_preamble
from vero.curation.stages.base import (
    StageContext,
    StageResult,
    StageRunner,
    compose_prompt,
)


class SelectStage(StageRunner):
    name = "select"
    human_review = True

    def _build_prompt(self, ctx: StageContext) -> str:
        curation_dir = ctx.curation_dir

        body = [
            f"Read the annotated discovery files in `{curation_dir}/discovery/`.",
            "Parse the checkbox selections ([x] = selected, [ ] = not selected).",
            "If no `[x]` selections exist in the discovery markdowns, do NOT",
            "stall or infer from source_index.selected. Use a conservative",
            "default selection from `discovery_report.json`/`api.md`: select",
            "all items whose discovery category is `api` or `spec`, include",
            "all `type`, `api_helper`, and `spec_helper` items needed to state",
            "or implement those selected items, and mark every other item",
            "`dropped_with_reason` unless it is required by closure.",
            "Record this fallback in `closure_warnings`.",
            "Also read `.vero/source_index.json` if present. Use it ONLY as",
            "a neutral global entity registry for source names, kinds, source",
            "locations, and signatures. Do not inherit roles from source_index;",
            "all source_index roles/dispositions are unclassified inventory.",
            "Every selected or dependency-closure item must get an explicit",
            "selection-stage role (`scored_api`, `scored_spec`, `api_helper`,",
            "`semantic_model`, `spec_helper`, `trusted_theory`, `trusted_external`,",
            "`reference_api`, `dropped_with_reason`, `proof_helper_task`,",
            "`trusted_theorem`, or `requires_human_review`).",
            "",
            "Compute the transitive dependency closure of selected items.",
            "If an item is needed only as semantic interpretation infrastructure",
            "(for example F2R-style functions), classify it as `semantic_model`,",
            "not as dropped context. Use `spec_helper` only for fixed vocabulary",
            "needed to state specs: types, inductives, structures, predicates,",
            "definitions, notation, and semantic models. Do not classify a source",
            "`Theorem`/`Lemma`/Lean `theorem`/`lemma`/Dafny `lemma` as",
            "`spec_helper` merely because it appears in dependency closure.",
            "A theorem/lemma must be classified as one of: `scored_spec`",
            "when it is an evaluated benchmark obligation, `proof_helper_task` when the",
            "solver should prove it as a helper, `trusted_theorem` only when it",
            "has an explicit real proof or human-review justification,",
            "`dropped_with_reason` when unused, or `requires_human_review` when",
            "unclear. If a theorem/definition would be turned into an axiom,",
            "classify it as `requires_human_review` unless it is a real external",
            "boundary.",
            "Definitions/predicates that are required only to state specs",
            "remain `spec_helper` and must be provided with real definitions.",
            "`proof_helper_task` is only for theorem/lemma proof obligations,",
            "or for proof-bearing definitions explicitly reviewed as tasks.",
            "Do not move ordinary Prop-valued predicate definitions such as",
            "`in_alphabet`, `not_null`, or `cover_min` into specs merely",
            "because they mention propositions; they are vocabulary unless",
            "the selection explicitly scores their construction.",
            "Reject proof-bearing scored APIs by default. A selected `api` whose",
            "return type is a subtype/dependent pair/existence/certificate",
            "(for example `{x | P x}`, `Subtype`, sigma, `Exists`, or a pair",
            "carrying a proof) must be `requires_human_review` or",
            "`dropped_with_reason`; select an underlying computational API",
            "instead when one exists.",
            "Assign translation layers (bottom-up by dependency depth).",
            "Plan the Lean file layout mirroring the source structure.",
            "",
            f"Write `{curation_dir}/selection.md` with the human-readable plan.",
            f"Write `{curation_dir}/selection_plan.json` with the machine-readable SelectionPlan.",
        ]

        return compose_prompt(skill_preamble("select"), body, ctx)

    async def run(self, ctx: StageContext) -> StageResult:
        from vero.curation.agent import call_agent

        prompt = self._build_prompt(ctx)
        if ctx.resume_session_id:
            prompt = "Continue the selection computation where you left off."

        _, session_id = await call_agent(
            model=ctx.config.model,
            permission_mode=ctx.config.permission_mode,
            prompt=prompt,
            tools=["Read", "Write", "Bash", "Grep", "Glob"],
            max_turns=ctx.config.max_turns_select,
            resume_session_id=ctx.resume_session_id,
            api_key=ctx.config.api_key,
            api_base_url=ctx.config.api_base_url,
            **ctx.config.agent_kwargs,
        )

        selection_md = ctx.curation_dir / "selection.md"
        selection_json = ctx.curation_dir / "selection_plan.json"
        output_files = []
        if selection_md.exists():
            output_files.append(str(selection_md))
        if selection_json.exists():
            output_files.append(str(selection_json))

        success = selection_md.exists() and selection_json.exists()

        return StageResult(
            stage=self.name,
            success=success,
            output_files=output_files,
            human_review_required=True,
            human_review_instructions=(
                f"Review {selection_md}\n"
                "- Check closure warnings\n"
                "- Verify layer assignments\n"
                "- Verify Lean file layout\n"
                f"Then re-run with --stage plan"
            ),
            error=(
                ""
                if success
                else "selection.md and selection_plan.json must both be produced"
            ),
            session_id=session_id or "",
        )
