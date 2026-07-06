"""PLAN stage — agent writes the authoritative translation plan.

Output contract (per docs/pipeline-schema.md):

- ``.vero/plan.json`` — authoritative, machine-readable plan
  consumed by translate + validate.
- ``.vero/plan/questions.md`` (optional) — human-facing questions.

The ``vero-plan`` skill (``.claude/skills/vero-plan/SKILL.md``) defines
the JSON schema and field-by-field guidance; this stage invokes the
skill-driven agent.
"""

from __future__ import annotations

import json
from pathlib import Path

from vero.curation.stages._skill_preamble import skill_preamble
from vero.curation.stages.base import (
    StageContext,
    StageResult,
    StageRunner,
    compose_prompt,
)

_ALLOWED_DISPOSITIONS = {
    "unclassified",
    "provided",
    "scored",
    "hidden",
    "dropped",
    "axiomatized",
    "opaque",
}

_DISPOSITION_SYNONYMS = {
    "given": "provided",
}


class PlanStage(StageRunner):
    name = "plan"
    human_review = True

    def _build_prompt(self, ctx: StageContext) -> str:
        curation_dir = ctx.curation_dir
        source_dir = ctx.source_dir
        repo_root = ctx.repo_root

        body = [
            "Load the `vero-plan` skill. Also load the matching",
            f"`vero-source-{{{ctx.config.source_language.value}}}` skill if available for language-specific",
            "classification + type mappings.",
            "",
            "## Inputs",
            "",
            f"- `{curation_dir}/selection_plan.json`",
            "  (approved selection with proposed packages + module grouping).",
            f"- `{curation_dir}/selection.md` (human-readable selection notes).",
            f"- `{curation_dir}/discovery_report.json`",
            "  (entity catalog with signatures + doc strings).",
            f"- `{curation_dir}/api.md` (discovered API catalog).",
            f"- `{curation_dir.parent}/.vero/source_index.json`",
            "  (no-LLM source-wide entity registry).",
            f"- `{curation_dir.parent}/config.yaml`",
            "  (project_name, benchmark_id, lean_version).",
            f"- Source code at `{source_dir}` — read the actual source to get exact signatures",
            "  and English doc comments.",
            "",
            "Use only files under this output workspace:",
            f"`{curation_dir.parent}`.",
            "Do not search other directories under `output/` for missing plan inputs;",
            "that would mix artifacts from unrelated runs.",
        ]
        if str(repo_root) != str(source_dir):
            body.append(
                f"- Repository root `{repo_root}` — README and docs for project context."
            )
        body.extend(
            [
                "",
                "## What to produce",
                "",
                "### 1. `.vero/plan.json` — authoritative translation plan",
                "",
                "Follow the schema in `docs/pipeline-schema.md` (plan.json section)",
                "and the `vero-plan` skill. Minimum required fields:",
                "",
                "```json",
                "{",
                '  "version": 1,',
                '  "api_namespace": "<Namespace>",',
                '  "packages": [{',
                '    "name": "<Project>", "is_root": true,',
                '    "bundle_type": "<Project>Bundle",',
                '    "repo_impl_field": "<lowerCamelCase>",',
                '    "modules": [{',
                '      "name": "<Module>",',
                '      "upstream_files": ["..."],',
                '      "types": [{"name": "...", "lean_form": "...", "is_foundation": true|false}],',
                '      "apis": [{"upstream_name": "...", "lean_name": "...", "sig_abbrev": "...",',
                '                "lean_type": "...", "opaque": false, "role": "scored_api",',
                '                "disposition": "scored", "source_id": "...", "nl_description": "..."}],',
                '      "specs": [{"name": "spec_...", "nl_description": "...", "lean_form": "...",',
                '                 "apis_referenced": ["..."], "source_theorem": "...",',
                '                 "equivalence_status": "equivalent|weaker|stronger|unclear",',
                '                 "semantic_bridge_required": [],',
                '                 "curator_intended_truth": "prove|disprove|unsat|sat|unknown"}],',
                '      "ref_impls": [{"name": "...", "namespace": "Bank.Ref", "lean_form": "def ..."}]',
                "    }]",
                "  }],",
                '  "test_cases": [{"name": "...", "nl_description": "...", "lean_form": "#guard ..."}]',
                "}",
                "```",
                "",
                "### 2. `.vero/plan/questions.md` (only if needed)",
                "",
                "Bulleted list of translation questions for the human. See the",
                "`vero-plan` skill for format.",
                "",
                "## Hard rules",
                "",
                "- **Spec bodies use `impl.<repo_impl_field>.<lean_name>`**",
                "  (e.g. `impl.bankLedger.createAccount`), NEVER bare `impl.<fn>`.",
                "- Every name used in `lean_form`, `lean_type`, specs, helpers,",
                "  and tests must be a valid Lean identifier that is either",
                "  defined in this plan, imported from Lean/Mathlib, or accessed",
                "  through the implementation bundle as",
                "  `impl.<repo_impl_field>.<lean_name>`. Do not invent helper",
                "  names such as `impl_computeFoo`, and do not use bare API",
                "  names like `foo` when the planned API name is available only",
                "  through the bundle.",
                "- Preserve and use the exact `lean_name`s chosen in this plan.",
                "  If you rename an upstream item, update every reference to the",
                "  renamed Lean identifier consistently. Do not mix snake_case",
                "  source names with camelCase Lean names unless both are defined.",
                "- Types with `is_foundation: true` must live in the module every",
                "  other Impl in the package imports.",
                "- Every API in `selection_plan.json` appears in exactly one module's",
                "  `apis[]`; every spec in `selection_plan.json` appears in exactly one",
                "  `specs[]`.",
                "- Every planned API/spec/helper carries role/disposition/source",
                "  metadata when source_index/discovery/selection contains the",
                "  entity. For APIs include `role`, `disposition`, and `source_id`.",
                "  For specs include `source_theorem`, `equivalence_status`, and",
                "  `semantic_bridge_required` even when the bridge list is empty.",
                "- Supported `disposition` values are exactly:",
                "  `unclassified`, `provided`, `scored`, `hidden`, `dropped`,",
                "  `axiomatized`, and `opaque`. Use `provided` for fixed",
                "  curator/source-given vocabulary such as translated types and",
                "  spec helpers; do not write `given`.",
                "- **Every translated plan item must be source-backed.** Every",
                "  entry in `types[]`, `apis[]`, `api_helpers[]`,",
                "  `spec_helpers[]`, `specs[]`, and `ref_impls[]` must carry",
                "  source provenance that resolves to `.vero/source_index.json`",
                "  or to a concrete source declaration from discovery/selection.",
                "  Include a real `source_id` whenever possible, plus",
                "  `source_file`, `source_line`, `upstream_name` or",
                "  `source_theorem`, and `source_signature` when available.",
                "  Do not create generated source ids, blank source files,",
                "  placeholder helpers, sentinel predicates, source-token",
                "  wrappers, or review-marker definitions to stand in for an",
                "  upstream item. If a selected theorem/API/helper cannot be",
                "  translated faithfully now, keep it out of the translated",
                "  item lists and record it only as review-only/untranslated with",
                "  a reason; do not emit it as a scored `spec` or helper.",
                '- `requires_human_review` and `equivalence_status: "unclear"`',
                "  are not allowed inside translated/scored item lists. Those",
                "  statuses mean the item is not ready for translation; move it",
                "  to review-only/untranslated metadata until a faithful Lean",
                "  form is available.",
                "- No `scored_api` may have a proof-bearing return type unless",
                "  explicitly marked `requires_human_review` with a justification.",
                "  In particular, do not classify APIs returning Lean `Subtype`,",
                "  `{x : T // P x}`, `Σ`/sigma values, `Exists`, or dependent",
                "  pairs containing correctness proofs as normal scored APIs.",
                "  Select the underlying computational helper as the scored API",
                "  and move correctness obligations into `specs[]`, or stop and",
                "  ask for human review.",
                "- Semantic models such as `F2R` must be represented as",
                "  `semantic_model`/`spec_helper`, not silently dropped.",
                "- Translate definitions and predicates faithfully from the source.",
                "  Do not replace a source definition with a convenient surrogate,",
                "  sketch, simplification, over-strong property, or approximate",
                "  theorem. If an exact translation is unclear, write a question in",
                "  `.vero/plan/questions.md` and mark the affected spec/helper",
                '  `equivalence_status: "unclear"` or `requires_human_review`.',
                "- Do not make a generated helper definition depend on missing",
                "  typeclass assumptions. For example, if a definition uses `=`",
                "  decision or filtering by inequality, its `lean_form` must include",
                "  the required `[DecidableEq A]` argument or avoid that operation.",
                "- Do not place tactics or proof terms such as `by omega`, `by simp`,",
                "  or `by exact ...` inside spec proposition expressions unless the",
                "  source item is explicitly a provided theorem proof. Specs should",
                "  state propositions; they should not smuggle proof scripts into",
                "  index terms.",
                "- Do not convert upstream definitions/theorems into Lean `axiom`s",
                "  unless the role is `trusted_external` or `requires_human_review`",
                "  with a clear reason.",
                "- If a source theorem is decomposed into several structural specs,",
                "  record `equivalence_status` and the bridge lemmas required to",
                "  recover the source theorem.",
                "- Arrows in `lean_type` / `lean_form` are `→` (Unicode), not `->`.",
                "- Before finishing, self-check `plan.json`: JSON parses; all API",
                "  `sig_abbrev`s are unique; all `apis_referenced` and",
                "  `spec_helpers_referenced` resolve to planned names; no",
                "  `lean_form` contains undefined identifiers introduced by the",
                "  planner; every translated item has non-generated source",
                "  provenance resolving to `.vero/source_index.json`; and item",
                "  counts match `selection_plan.json` or are explicitly accounted",
                "  for as review-only/untranslated.",
                "- Do NOT produce markdown plan files — `plan.json` is the contract.",
            ]
        )

        return compose_prompt(
            skill_preamble("plan", ctx.config.source_language), body, ctx
        )

    async def run(self, ctx: StageContext) -> StageResult:
        from vero.curation.agent import call_agent

        prompt = self._build_prompt(ctx)
        if ctx.resume_session_id:
            prompt = "Continue writing `.vero/plan.json` where you left off."

        _, session_id = await call_agent(
            model=ctx.config.model,
            permission_mode=ctx.config.permission_mode,
            prompt=prompt,
            tools=["Read", "Write", "Bash", "Grep", "Glob"],
            max_turns=ctx.config.max_turns_plan,
            resume_session_id=ctx.resume_session_id,
            api_key=ctx.config.api_key,
            api_base_url=ctx.config.api_base_url,
            **ctx.config.agent_kwargs,
        )

        # Primary output is .vero/plan.json (workspace-relative).
        vero_dir = ctx.curation_dir.parent / ".vero"
        plan_json = vero_dir / "plan.json"
        questions_md = vero_dir / "plan" / "questions.md"
        output_files = []
        if plan_json.exists():
            output_files.append(str(plan_json))
        if questions_md.exists():
            output_files.append(str(questions_md))

        source_index_json = ctx.curation_dir.parent / ".vero" / "source_index.json"
        success, error = _validate_plan_json(plan_json, source_index_json)

        return StageResult(
            stage=self.name,
            success=success,
            output_files=output_files,
            human_review_required=True,
            human_review_instructions=(
                f"Review the translation plan at {plan_json}\n"
                f"Answer any questions at {questions_md if questions_md.exists() else '(no questions raised)'}\n"
                "- Confirm api_namespace, package name, bundle_type, repo_impl_field\n"
                "- Confirm every API has a unique sig_abbrev and correct lean_type\n"
                "- Confirm every spec body uses `impl.<repo_impl_field>.<fn>`\n"
                "- Edit plan.json directly if anything is off\n"
                "Then re-run with --stage translate"
            ),
            error=error,
            session_id=session_id or "",
        )


_PLAN_ITEM_COLLECTIONS = (
    "types",
    "apis",
    "api_helpers",
    "spec_helpers",
    "specs",
    "ref_impls",
)


def _source_index_entities(source_index: dict | None) -> list:
    if not isinstance(source_index, dict):
        return []
    entities = source_index.get("entities")
    if entities is None:
        entities = source_index.get("items")
    return entities if isinstance(entities, list) else []


def _source_name_variants(name: str) -> set[str]:
    clean = name.strip()
    tail = clean.rsplit(".", 1)[-1]
    return {clean, tail, clean.lower(), tail.lower()}


def _source_id_parts(source_id: str) -> tuple[str | None, str | None]:
    parts = source_id.split(":")
    if len(parts) >= 2 and parts[0] and parts[1]:
        return parts[0], parts[1]
    return None, None


def _source_index_lookup(
    source_index: dict | None,
) -> tuple[set[str], set[tuple[str, str]]]:
    names: set[str] = set()
    file_names: set[tuple[str, str]] = set()
    for entity in _source_index_entities(source_index):
        if not isinstance(entity, dict):
            continue
        source_file = entity.get("source_file")
        for key in ("name", "qualified_name", "upstream_name"):
            value = entity.get(key)
            if isinstance(value, str) and value.strip():
                variants = _source_name_variants(value)
                names.update(variants)
                if isinstance(source_file, str) and source_file.strip():
                    for variant in variants:
                        file_names.add((source_file.strip(), variant))
    return names, file_names


def _plan_item_source_names(item: dict) -> set[str]:
    names: set[str] = set()
    for key in ("upstream_name", "source_theorem", "source_name"):
        value = item.get(key)
        if isinstance(value, str) and value.strip():
            names.update(_source_name_variants(value))
    source_id = item.get("source_id")
    if isinstance(source_id, str):
        _source_file, source_name = _source_id_parts(source_id)
        if source_name:
            names.update(_source_name_variants(source_name))
    return names


def _has_non_generated_source(item: dict) -> bool:
    source_id = item.get("source_id")
    if isinstance(source_id, str):
        clean = source_id.strip()
        if (
            clean.startswith("generated:")
            or clean.startswith("placeholder:")
            or clean.endswith(":generated")
        ):
            return False
        if clean:
            return True
    source_file = item.get("source_file")
    if isinstance(source_file, str):
        clean_file = source_file.strip()
        if clean_file and not clean_file.startswith("generated:"):
            line = item.get("source_line")
            return not isinstance(line, int) or line > 0
    for key in ("upstream_name", "source_theorem", "source_name"):
        value = item.get(key)
        if isinstance(value, str) and value.strip():
            return True
    return False


def _resolves_to_source_index(
    item: dict,
    names: set[str],
    file_names: set[tuple[str, str]],
) -> bool:
    if not names and not file_names:
        return True
    source_id = item.get("source_id")
    if isinstance(source_id, str):
        source_file, source_name = _source_id_parts(source_id)
        if source_name:
            variants = _source_name_variants(source_name)
            if variants & names:
                return True
            if source_file and any(
                (source_file, variant) in file_names for variant in variants
            ):
                return True
    source_file = item.get("source_file")
    if isinstance(source_file, str) and source_file.strip():
        for source_name in _plan_item_source_names(item):
            if (source_file.strip(), source_name) in file_names:
                return True
    return bool(_plan_item_source_names(item) & names)


def _iter_plan_items(plan: dict):
    for pkg in plan.get("packages", []):
        if not isinstance(pkg, dict):
            continue
        pkg_name = pkg.get("name", "<package>")
        for mod in pkg.get("modules", []):
            if not isinstance(mod, dict):
                continue
            mod_name = mod.get("name", "<module>")
            for collection in _PLAN_ITEM_COLLECTIONS:
                entries = mod.get(collection, [])
                if not isinstance(entries, list):
                    continue
                for idx, raw in enumerate(entries):
                    if not isinstance(raw, dict):
                        continue
                    name = (
                        raw.get("lean_name")
                        or raw.get("name")
                        or raw.get("upstream_name")
                        or raw.get("source_theorem")
                        or f"#{idx}"
                    )
                    yield raw, f"{pkg_name}.{mod_name}.{collection}.{name}"


def _translated_item_is_unresolved(item: dict, collection: str) -> str:
    if item.get("requires_human_review"):
        return "requires_human_review item is in a translated plan list"
    disposition = item.get("disposition")
    if isinstance(disposition, str) and disposition in {
        "review_only",
        "requires_human_review",
        "untranslated",
    }:
        return f"disposition={disposition!r} item is in a translated plan list"
    status = item.get("equivalence_status")
    if collection == "specs" and status == "unclear":
        return "spec has equivalence_status='unclear'"
    return ""


def _normalize_plan_metadata(plan: dict) -> bool:
    changed = False
    for item, _location in _iter_plan_items(plan):
        disposition = item.get("disposition")
        if isinstance(disposition, str) and disposition in _DISPOSITION_SYNONYMS:
            item["disposition"] = _DISPOSITION_SYNONYMS[disposition]
            changed = True
    return changed


def _load_source_index(source_index_json: Path | None) -> dict | None:
    if source_index_json is None or not source_index_json.exists():
        return None
    try:
        data = json.loads(source_index_json.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return None
    return data if isinstance(data, dict) else None


def _validate_plan_json(
    plan_json: Path,
    source_index_json: Path | None = None,
) -> tuple[bool, str]:
    if not plan_json.exists():
        return False, f"plan.json must be produced at {plan_json}"
    try:
        plan = json.loads(plan_json.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        return False, f"invalid plan.json at {plan_json}: {exc}"
    if not isinstance(plan, dict):
        return False, f"plan.json at {plan_json} must be a JSON object"
    if _normalize_plan_metadata(plan):
        plan_json.write_text(json.dumps(plan, indent=2) + "\n", encoding="utf-8")
    packages = plan.get("packages")
    if not isinstance(packages, list) or not packages:
        return False, f"plan.json at {plan_json} must contain nonempty packages[]"
    modules = [
        mod
        for pkg in packages
        if isinstance(pkg, dict)
        for mod in pkg.get("modules", [])
        if isinstance(mod, dict)
    ]
    if not modules:
        return False, f"plan.json at {plan_json} must contain at least one module"
    if not any(isinstance(pkg, dict) and pkg.get("is_root") for pkg in packages):
        return (
            False,
            f"plan.json at {plan_json} must mark one package with is_root=true",
        )
    source_index = _load_source_index(source_index_json)
    source_names, source_file_names = _source_index_lookup(source_index)
    errors: list[str] = []
    for item, location in _iter_plan_items(plan):
        collection = location.split(".")[-2] if "." in location else ""
        disposition = item.get("disposition")
        if isinstance(disposition, str) and disposition not in _ALLOWED_DISPOSITIONS:
            errors.append(
                f"{location}: unsupported disposition={disposition!r}; "
                f"expected one of {sorted(_ALLOWED_DISPOSITIONS)}"
            )
        if not _has_non_generated_source(item):
            errors.append(f"{location}: missing or generated source provenance")
            continue
        if not _resolves_to_source_index(item, source_names, source_file_names):
            errors.append(
                f"{location}: source provenance does not resolve to source_index.json"
            )
        unresolved_reason = _translated_item_is_unresolved(item, collection)
        if unresolved_reason:
            errors.append(
                f"{location}: {unresolved_reason}; move it to review-only/untranslated metadata"
            )
    if errors:
        sample = "\n".join(f"- {err}" for err in errors[:25])
        suffix = f"\n... {len(errors) - 25} more" if len(errors) > 25 else ""
        return (
            False,
            "plan.json source provenance check failed; every translated plan item "
            "must correspond to a real upstream source item:\n"
            f"{sample}{suffix}",
        )
    return True, ""
