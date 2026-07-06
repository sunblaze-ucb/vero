"""Executor agent — translates a single module (Impl + Spec).

Each executor gets a focused prompt scoped to one module and calls
``call_agent()`` to produce ``Impl/<Module>.lean`` and
``Spec/<Module>.lean``.
"""

from __future__ import annotations

from pathlib import Path

from loguru import logger

from vero.curation.orchestrator.models import ExecutorResult, TranslationUnit
from vero.curation.stages._skill_preamble import skill_preamble


def _build_executor_prompt(
    unit: TranslationUnit,
    project_dir: Path,
    source_dir: Path,
    shared_context: str,
    language: str,
    api_namespace: str,
) -> str:
    """Build a module-scoped prompt for the executor agent."""
    preamble = skill_preamble("translate", language)

    types_block = ""
    if unit.types:
        types_block = "### Types to define in this module\n\n"
        for t in unit.types:
            types_block += f"- `{t.get('name', '')}`: `{t.get('lean_form', '')}`"
            if t.get("is_foundation"):
                types_block += " (foundation type — other modules import this)"
            types_block += "\n"

    apis_block = ""
    if unit.apis:
        apis_block = "### APIs to implement\n\n"
        for a in unit.apis:
            apis_block += (
                f"- `{a.get('lean_name', '')}` : `{a.get('lean_type', '')}`\n"
                f"  Sig abbrev: `{a.get('sig_abbrev', '')}`\n"
                f"  Description: {a.get('nl_description', 'N/A')}\n"
            )
            if a.get("opaque"):
                apis_block += "  **OPAQUE** — emit `opaque` + axiom, not `sorry`\n"
    else:
        apis_block = (
            "### APIs to implement\n\n"
            "This module has NO assigned scored APIs. Do not emit any API sig "
            "abbrev, `Huffman.*` API definition, `code` marker, `code_aux` "
            "marker, or Bundle field for this module. Source definitions not "
            "listed above are intentionally out of scope or require human "
            "review.\n"
        )

    api_helpers_block = ""
    if unit.api_helpers:
        api_helpers_block = "### API helpers to emit as frozen definitions\n\n"
        for h in unit.api_helpers:
            name = h.get("lean_name", h.get("name", ""))
            api_helpers_block += (
                f"- `{name}`: {h.get('nl_description', 'N/A')}\n"
                f"  Lean form:\n"
                f"  ```lean\n{h.get('lean_form', '')}\n  ```\n"
            )

    spec_helpers_block = ""
    if unit.spec_helpers:
        spec_helpers_block = "### Spec helpers to emit as frozen definitions\n\n"
        for h in unit.spec_helpers:
            name = h.get("lean_name", h.get("name", ""))
            spec_helpers_block += (
                f"- `{name}`: {h.get('nl_description', 'N/A')}\n"
                f"  Lean form:\n"
                f"  ```lean\n{h.get('lean_form', '')}\n  ```\n"
            )

    specs_block = ""
    if unit.specs:
        specs_block = "### Specs to write (frozen, NO markers)\n\n"
        for s in unit.specs:
            specs_block += (
                f"- `{s.get('name', '')}`: {s.get('nl_description', 'N/A')}\n"
                f"  Lean form: `{s.get('lean_form', '')}`\n"
                f"  Truth: {s.get('curator_intended_truth', 'unknown')}\n"
            )

    upstream_files = ", ".join(f"`{f}`" for f in unit.upstream_files) or "N/A"
    deps_block = ""
    if unit.dependencies:
        dep_imports = "\n".join(
            f"import {unit.package_name}.Impl.{dep}" for dep in unit.dependencies
        )
        deps_block = (
            "### Required imports from earlier modules\n\n"
            "These modules own vocabulary referenced by this module. Import them; "
            "do not redefine their symbols.\n\n"
            f"```lean\n{dep_imports}\n```\n"
        )

    prompt = f"""{preamble}

## Task

You are an **executor agent** responsible for translating exactly ONE module:
**{unit.module_name}** (package: {unit.package_name}).

### Your output files

1. `{project_dir}/{unit.impl_path}` — Impl file with types, namespace {api_namespace},
   sig abbrevs, and function stubs wrapped in `!benchmark code` markers.
   Write **reference implementations** inside the markers (not `sorry`).
   Add `-- !curation @review v1 [ ] <name>` annotations per API.

2. `{project_dir}/{unit.spec_path}` — Spec file with frozen specs and any
   RepoImpl-dependent spec helpers. Specs use `impl.<repo_impl_field>.<fn>`
   access pattern. If this module has listed specs or a spec helper whose Lean
   form mentions `RepoImpl` / `impl.<repo_impl_field>`, this file is required.
   Each listed spec must be defined as:
   `def spec_name (impl : RepoImpl) : Prop := <listed prop body>`.

### Canonical shape

Read `reference/BankLedger/` for the exact file structure, marker placement,
and naming conventions. Specifically look at a matching Impl/Spec pair.

### Source files

Upstream source for this module: {upstream_files}
Source directory: `{source_dir}`
Only inspect this module's upstream files under `{source_dir}` plus the
target files under `{project_dir}`. Do not search from the repository root
or any parent directory; use `Read`, `Glob`, or scoped `rg --files` only
inside `{source_dir}` and `{project_dir}`.

{deps_block}
{types_block}
{spec_helpers_block}
{api_helpers_block}
{apis_block}
{specs_block}
### Shared context from earlier layers

{shared_context if shared_context else "(This is a layer-0 module — no prior context.)"}

### Hard rules

- File ownership is strict. You may write or edit only:
  `{project_dir}/{unit.impl_path}` and `{project_dir}/{unit.spec_path}`.
  Do not edit any other `Impl/*.lean`, `Spec/*.lean`, glue file, manifest,
  lake file, or dependency module. If another module is wrong or an import
  collision prevents this module from compiling, stop and report the issue
  instead of repairing that other module.
- Only 7 `!benchmark` keys: imports, global_aux, code, code_aux, proof, proof_aux, claim.
- `imports` marker sits immediately after `import` lines, BEFORE module docstring.
- `proof_aux` at file level — never between `by` and proof body.
- Spec/*.lean has NO markers of any prefix.
- No `Sig.lean`, no `Types.lean` — types + sigs live in Impl/*.
- Emit listed `spec_helpers` and `api_helpers` as frozen, marker-free
  definitions.
- If a helper Lean form mentions `RepoImpl` or `impl.<repo_impl_field>`, emit
  that helper in the module's Spec/*.lean file before the specs, not in
  Impl/*.lean. Pure helpers that do not mention RepoImpl belong in Impl/*.lean.
- Do not add helper definitions to Bundle.lean; only scored APIs become Bundle
  fields.
- Emit only the types, spec_helpers, api_helpers, APIs, and specs assigned
  above for this module. If you need a symbol that is not assigned above, import
  the module that owns it instead of creating an approximation or duplicate
  root-level definition.
- Do not invent Coq compatibility aliases such as `In`, `NoDup`, `length`,
  `map`, `code`, `btree`, or `unique_key` unless they are explicitly listed in
  this module's assigned items above. Duplicate root-level names make the final
  benchmark impossible to assemble.
- Write real reference implementations inside `code` markers (not `sorry`).
- Follow role/disposition metadata from plan.json and `.vero/source_index.json`.
  Semantic-model helpers must remain explicit helpers; do not drop them or replace
  them with axioms.
- Specs for scored APIs must use `impl.<repo_impl_field>.<api>`. Do not reference
  a scored API through a frozen namespace definition unless the plan marks it as
  `reference_api` or `reference_allowed`.
- If translating a source theorem into decomposed structural specs, preserve the
  `source_theorem`, `equivalence_status`, and `semantic_bridge_required` metadata.
- Do NOT write Bundle.lean, Harness.lean, Test.lean, or the root hub —
  those are assembled separately.
- Every shell command that can traverse files or invoke Lean/Lake must use
  `timeout`, so verification cannot hang the layer.

After writing both files, verify with:
```bash
cd {project_dir} && timeout 120s lake env lean {unit.impl_path}
```
"""
    return prompt


def _has_repo_impl_spec_helper(unit: TranslationUnit) -> bool:
    """Return true when a spec helper must live in Spec rather than Impl."""
    for helper in unit.spec_helpers:
        lean_form = helper.get("lean_form", "")
        if "RepoImpl" in lean_form or "impl." in lean_form:
            return True
    return False


async def run_executor(
    unit: TranslationUnit,
    project_dir: Path,
    source_dir: Path,
    shared_context: str,
    language: str,
    api_namespace: str,
    model: str,
    permission_mode: str,
    max_turns: int,
    api_key: str | None = None,
    api_base_url: str | None = None,
    enable_lean_mcp: bool = True,
    agent_kind: str = "claude",
    codex_auth_mode: str = "api",
    codex_sandbox_mode: str = "danger-full-access",
    codex_timeout_seconds: int = 1800,
    codex_network_access: bool = False,
    codex_model_reasoning_effort: str | None = None,
) -> ExecutorResult:
    """Run an executor agent for a single module translation."""
    from vero.curation.agent import build_lean_mcp_servers, call_agent
    from vero.curation.marker import validate_markers

    logger.info(f"[executor] Starting module: {unit.module_name} (layer {unit.layer})")

    prompt = _build_executor_prompt(
        unit=unit,
        project_dir=project_dir,
        source_dir=source_dir,
        shared_context=shared_context,
        language=language,
        api_namespace=api_namespace,
    )

    mcp_servers = None
    if enable_lean_mcp:
        mcp_servers = build_lean_mcp_servers(str(project_dir))

    try:
        _, session_id = await call_agent(
            model=model,
            permission_mode=permission_mode,
            prompt=prompt,
            tools=["Read", "Write", "Edit", "Bash", "Grep", "Glob"],
            max_turns=max_turns,
            api_key=api_key,
            api_base_url=api_base_url,
            mcp_servers=mcp_servers,
            agent_kind=agent_kind,
            codex_auth_mode=codex_auth_mode,
            codex_sandbox_mode=codex_sandbox_mode,
            codex_timeout_seconds=codex_timeout_seconds,
            codex_network_access=codex_network_access,
            codex_model_reasoning_effort=codex_model_reasoning_effort,
        )
    except Exception as exc:
        logger.error(f"[executor] Agent failed for {unit.module_name}: {exc}")
        return ExecutorResult(
            module_name=unit.module_name,
            success=False,
            error=str(exc),
        )

    # Read back written files
    impl_path = project_dir / unit.impl_path
    spec_path = project_dir / unit.spec_path

    impl_content = ""
    spec_content = ""
    if impl_path.exists():
        impl_content = impl_path.read_text(encoding="utf-8")
    if spec_path.exists():
        spec_content = spec_path.read_text(encoding="utf-8")

    if not impl_content:
        return ExecutorResult(
            module_name=unit.module_name,
            success=False,
            error=f"Impl file not written: {unit.impl_path}",
            session_id=session_id or "",
        )

    # Validate markers in impl file
    marker_errors = validate_markers(impl_content)
    # Check for any markers in spec (there should be none)
    spec_required = bool(unit.specs) or _has_repo_impl_spec_helper(unit)
    if spec_required and not spec_content:
        marker_errors.append(f"Spec file not written: {unit.spec_path}")
    if spec_content and "!benchmark" in spec_content:
        marker_errors.append(f"{unit.spec_path}: Spec file must have NO markers")
    for spec in unit.specs:
        spec_name = spec.get("name", "")
        if spec_name and spec_content and f"def {spec_name}" not in spec_content:
            marker_errors.append(
                f"{unit.spec_path}: listed spec {spec_name!r} not found"
            )

    success = len(marker_errors) == 0

    logger.info(
        f"[executor] Module {unit.module_name}: "
        f"{'OK' if success else 'ERRORS'} "
        f"({len(marker_errors)} marker errors)"
    )

    return ExecutorResult(
        module_name=unit.module_name,
        success=success,
        impl_content=impl_content,
        spec_content=spec_content,
        marker_errors=marker_errors,
        session_id=session_id or "",
    )
