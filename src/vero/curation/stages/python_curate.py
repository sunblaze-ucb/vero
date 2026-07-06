"""PYTHON_CURATE stage — agent-driven Python→Lean curation.

Replaces the deterministic ``PythonFromJsonStage`` + post-hoc
``PythonAdjustBodiesStage`` pair with a single agent-driven stage.

The agent reads ``benchmark.json`` as a *reference* for API selection and
signatures (it is allowed to drop / rename / regroup), and it reads
``original_python/`` as the *truth* source for both shape and Impl
bodies. It emits a complete bundle-paradigm Lean tree (Impl / Spec /
Bundle / Harness / Test / manifest) with real Impls — no ``sorry`` in
``!benchmark code`` slots. Spec files are *empty stubs* at this stage;
``spec_write`` runs separately when the user OKs.

Single-agent (orchestrator-overhead is wasted at typical Python repo
scale: 1–10 modules, 5–30 APIs).

Skills: ``vero-translate`` + ``vero-source-python`` + language pitfalls.
"""

from __future__ import annotations

from pathlib import Path

from vero.curation.lean_project import to_project_name
from vero.curation.stages._skill_preamble import skill_preamble
from vero.curation.stages.base import (
    StageContext,
    StageResult,
    StageRunner,
    compose_prompt,
)
from vero.curation.stages.python_adjust_bodies import (
    _read_root_package,
    _resolve_python_source_dir,
    _run_lake_build,
    count_unfilled_code_bodies,
)


class PythonCurateStage(StageRunner):
    """Agent-driven Python→Lean curation: full scaffold + Impl fill."""

    name = "python_curate"
    human_review = True

    def _project_dir(self, ctx: StageContext) -> Path:
        return ctx.lean_output_dir / to_project_name(ctx.config.benchmark_id)

    def _build_prompt(
        self,
        ctx: StageContext,
        project_dir: Path,
        benchmark_json: Path,
        python_source_dir: Path,
        nl_docs_dir: Path | None,
        repo_root: Path,
        lean_version: str,
    ) -> str:
        preamble = skill_preamble("translate", ctx.config.source_language)
        nl_line = (
            f"- **NL docs** (optional context): `{nl_docs_dir}/`"
            if nl_docs_dir is not None and nl_docs_dir.exists()
            else "- **NL docs**: not present for this repo."
        )
        body = [
            "## Goal — agent-driven Python → Lean curation",
            "",
            "Produce a complete, `lake build`-clean Lean 4 project in the",
            "ratified bundle paradigm. `benchmark.json` is your API-selection",
            "and signature *reference* — it tells you what's expected, but you",
            "have full discretion to add helpers, drop irrelevant items,",
            "rename, regroup, or change generic handling for a clean Lean",
            "translation. `original_python/` is the *truth* for the actual",
            "implementation behaviour. The reference exemplar at",
            f"`{repo_root}/reference/BankLedger/` shows the canonical output",
            "layout in its simplest form (4 modules, 10 APIs, 11 specs).",
            "",
            "## Inputs",
            "",
            f"- **benchmark.json** (reference): `{benchmark_json}`",
            f"- **Python source** (truth): `{python_source_dir}/`",
            nl_line,
            f"- **Reference exemplar**: `{repo_root}/reference/BankLedger/`",
            "",
            "## Output target",
            "",
            f"The complete Lean project must land at `{project_dir}/`:",
            "",
            "```",
            f"{project_dir.name}/",
            "  lakefile.toml",
            "  lean-toolchain",
            "  manifest.json                 # bundle-paradigm metadata",
            "  <Project>.lean                # root hub (imports every module)",
            "  <Project>/",
            "    Bundle.lean                 # one structure, one field per API",
            "    Harness.lean                # RepoImpl + canonical + joint_unsat macro",
            "    Test.lean                   # #guard tests from benchmark.json",
            "    Impl/<Module>.lean          # types + sig abbrevs + REAL Impls",
            "    Spec/<Module>.lean          # namespace + placeholder ONLY",
            "```",
            "",
            "Mirror the structure of `reference/BankLedger/` exactly. The",
            "manifest.json must match `reference/BankLedger/manifest.json`'s",
            "shape: `root_package`, `files{root_hub,harness,test,lakefile}`,",
            "`packages[].{name,bundle,bundle_type,repo_impl_field,modules[]}`,",
            "`packages[].modules[].{name,impl,spec,apis[],specs[]}`. For this",
            "stage `specs[]` is `[]` (spec_write fills later).",
            "",
            "## Hard rules",
            "",
            "1. **No `sorry` / `axiom` / `admit` anywhere in `!benchmark code`",
            "   blocks.** Every API body must be a real Lean translation of",
            "   the Python source. If the Python idiom has no obvious Lean",
            "   form, prefer `partial def` (annotated with",
            "   `-- @review human: termination via <reason>`) over `sorry`.",
            "   Modeling an external lib as `opaque` in `global_aux` is",
            "   acceptable when the upstream genuinely has no Lean equivalent",
            "   (e.g. crypto primitives, OS calls); add an `@review` note.",
            "2. **Generics use Lean's `variable` declaration.** When the",
            "   Python source has parametric types (the `benchmark.json` per-file",
            "   `variables` block declares them as e.g.",
            "   `{KT VT : Type} [BEq KT] [Hashable KT]`), emit one",
            "   `variable {KT VT : Type} [BEq KT] [Hashable KT]` line at the",
            "   top of the module's namespace. Lean will auto-include those",
            "   binders in every abbrev / def in scope. Keep abbrev / def",
            "   bodies clean — no per-decl binder repetition.",
            "3. **Bundle fields expand polymorphic binders inline.** The",
            "   `<Project>/Bundle.lean` structure itself takes NO type params.",
            "   For polymorphic APIs, the field type expands the abbrev's",
            "   binders: e.g. `get : ∀ {KT VT : Type} [BEq KT] [Hashable KT],",
            "   KT → BidictBase KT VT → Option VT`. Use `Bidict.GetSig` only",
            "   if you can elaborate it without explicit binders at the",
            "   structure-field site.",
            "4. **Spec files are stubs.** Each `<Project>/Spec/<Module>.lean`",
            "   must compile but contain only `namespace <Project>` (or the",
            "   matching submodule namespace) and a placeholder comment",
            "   `-- specs filled by spec_write stage`. No `def spec_*` lines.",
            "5. **`benchmark.json` is reference, not gospel.** You may drop",
            "   private / dunder / Python-specific helpers (`__repr__`,",
            "   `__hash__`, etc.) that don't make sense as benchmark APIs;",
            "   leave a `-- !curation @review v1` note when you do.",
            "6. **Test.lean uses `#guard` with bundle-qualified calls.**",
            "   Translate every `benchmark.json::test_cases` entry to a",
            "   `#guard <expected> = canonical.<pkg>.<api> <args...>` line.",
            "   Wrap any `#guard` that doesn't yet evaluate (e.g. depends on",
            "   an `opaque`) in a `/- BY curator -/ ... -/` comment block",
            "   with an `@review` note explaining why.",
            '7. **lakefile.toml** uses `srcDir = "."` and',
            '   `leanOptions = [{ name = "autoImplicit", value = false }]`',
            "   — same as `reference/BankLedger/lakefile.toml`.",
            f"8. **lean-toolchain** pins `leanprover/lean4:v{lean_version}`.",
            "",
            "## Approach (recommended)",
            "",
            "1. Read `benchmark.json` end-to-end. Note the per-file `variables`",
            "   blocks and per-API `params` lists (especially `kind ==",
            '   "InstanceImplicit"` / `"Implicit"`). These tell you which',
            "   modules need a Lean `variable` line and what binders to put",
            "   in the Bundle field.",
            "2. Read every `.py` file under `original_python/`. Identify the",
            "   public surface (matches `benchmark.json::files[*].public_apis`)",
            "   and the private helpers each public API depends on.",
            "3. Open `reference/BankLedger/Bundle.lean`, `Harness.lean`, and",
            "   one each of `Impl/*.lean` / `Spec/*.lean` for layout reference.",
            "4. Sketch the package + module layout. Default heuristic: one Lean",
            "   module per Python file (snake_case → CamelCase), one package",
            "   per benchmark.",
            "5. Emit `lakefile.toml`, `lean-toolchain`, the empty",
            "   `<Project>.lean` root hub, and the (initially empty)",
            "   `manifest.json`. Run `lake build` to confirm the project",
            "   bootstraps.",
            "6. For each module:",
            "   a. Emit `Impl/<Module>.lean` with `variable` (if generic),",
            "      types, signature abbrevs, and real Impls inside",
            "      `!benchmark code def=<name>` markers.",
            "   b. Emit `Spec/<Module>.lean` as a namespace + placeholder",
            "      comment.",
            "   c. Run `lake build`. Fix errors before moving on.",
            "7. Emit `Bundle.lean`, `Harness.lean`, `Test.lean` once all",
            "   modules compile.",
            "8. Update `manifest.json` to reflect the final layout. Confirm",
            "   round-trip: every listed API exists at its declared file/name.",
            "9. Final `lake build` must exit 0.",
            "",
            "## Verify before declaring done",
            "",
            f"1. `cd {project_dir} && lake build` exits 0.",
            "2. Zero word-boundary `sorry` / `axiom` / `admit` inside any",
            "   `!benchmark code def=*` block (after stripping comments).",
            "3. `manifest.json` parses and every listed",
            "   `packages[].modules[].apis[].name` exists in the declared",
            "   `packages[].modules[].impl` file.",
            "4. `Test.lean` has at least one `#guard` per public API where",
            "   `benchmark.json` provided test cases (those without test_cases",
            "   are exempt; note in an `@review` comment).",
            "5. The root hub `<Project>.lean` imports every module.",
            "",
            "## Stop conditions",
            "",
            "- Build clean + body check passes + manifest round-trips → done.",
            "- Build red after exhausting the turn budget → leave a status",
            "  summary in `<project_dir>/CURATION_STATUS.md` listing the",
            "  remaining errors and which Impls / files are pending.",
        ]
        return compose_prompt(
            preamble,
            body,
            ctx,
            guidance_header="## Human Guidance",
        )

    async def run(self, ctx: StageContext) -> StageResult:
        project_dir = self._project_dir(ctx)
        benchmark_json = ctx.source_dir / "benchmark.json"
        python_source_dir = _resolve_python_source_dir(ctx)
        nl_docs_dir = ctx.source_dir / "original_nl"
        nl_docs_arg = nl_docs_dir if nl_docs_dir.exists() else None

        if not benchmark_json.exists():
            return StageResult(
                stage=self.name,
                success=False,
                error=(
                    f"benchmark.json not found at {benchmark_json}. "
                    "PYTHON_CURATE expects <source_dir>/benchmark.json as "
                    "the API-selection reference."
                ),
            )
        if not python_source_dir.exists():
            return StageResult(
                stage=self.name,
                success=False,
                error=(
                    f"Python source dir not found at {python_source_dir}. "
                    "Expected <source_dir>/<python_context_path>/ "
                    "(default 'original_python')."
                ),
            )

        # Idempotent skip: project exists, builds clean, every code block
        # is non-sorry, AND manifest.json round-trips. The last condition
        # is load-bearing — without it, a partially-curated tree (Impls
        # compile but manifest is `{}`) would skip the agent and slip
        # through to the validate stage, which then fails with a flood of
        # `manifest_schema: missing required …` errors.
        if project_dir.exists():
            build_ok, _ = await _run_lake_build(project_dir)
            remaining = count_unfilled_code_bodies(project_dir)
            manifest_ok = _verify_manifest_and_specs(project_dir) is None
            if build_ok and remaining == 0 and manifest_ok:
                return StageResult(
                    stage=self.name,
                    success=True,
                    output_files=[str(project_dir)],
                    human_review_required=False,
                )

        # Persist benchmark_id back to the curation config so downstream
        # stages can resolve <project_dir> = lean_output_dir / <Package>.
        # Mirrors the behaviour of PythonFromJsonStage (which writes
        # benchmark_id into config.yaml on first scaffold).
        if not ctx.config.benchmark_id:
            try:
                import json as _json

                bj = _json.loads(benchmark_json.read_text(encoding="utf-8"))
                bid = bj.get("benchmark_id")
                if isinstance(bid, str) and bid:
                    ctx.config.benchmark_id = bid
                    ctx.config.save()
                    project_dir = self._project_dir(ctx)
            except (OSError, ValueError):
                pass

        from vero.curation.agent import call_agent

        prompt = self._build_prompt(
            ctx,
            project_dir,
            benchmark_json,
            python_source_dir,
            nl_docs_arg,
            ctx.repo_root,
            ctx.config.lean_version,
        )
        max_turns = getattr(
            ctx.config, "max_turns_python_curate", ctx.config.max_turns_translate * 2
        )
        _, session_id = await call_agent(
            model=ctx.config.model,
            permission_mode=ctx.config.permission_mode,
            prompt=prompt,
            tools=["Read", "Write", "Edit", "Bash", "Grep", "Glob"],
            max_turns=max_turns,
            resume_session_id=ctx.resume_session_id,
            api_key=ctx.config.api_key,
            api_base_url=ctx.config.api_base_url,
            **ctx.config.agent_kwargs,
        )

        # Post-agent verification.
        if not project_dir.exists():
            return StageResult(
                stage=self.name,
                success=False,
                error=(
                    f"Agent did not create the Lean project at {project_dir}. "
                    "Re-run with `--continue` or inspect the agent transcript."
                ),
                session_id=session_id or "",
            )

        build_ok, build_output = await _run_lake_build(project_dir)
        package = _read_root_package(project_dir) or to_project_name(
            ctx.config.benchmark_id
        )
        impl_root = project_dir / package / "Impl" if package else None
        impl_files = (
            sorted(str(p) for p in impl_root.rglob("*.lean"))
            if impl_root is not None and impl_root.exists()
            else []
        )
        all_files = (
            sorted(str(p) for p in project_dir.rglob("*.lean"))
            if project_dir.exists()
            else []
        )

        if not build_ok:
            return StageResult(
                stage=self.name,
                success=False,
                error=f"lake build failed after python_curate:\n{build_output[-1500:]}",
                output_files=all_files,
                human_review_required=True,
                human_review_instructions=(
                    f"Build failed at {project_dir}. Inspect output, then "
                    "re-run with `--stage python_curate --force` (fresh agent) "
                    "or `--continue` (resume the session)."
                ),
                session_id=session_id or "",
            )

        remaining_after = count_unfilled_code_bodies(project_dir)
        if remaining_after > 0:
            return StageResult(
                stage=self.name,
                success=False,
                error=(
                    f"build OK but {remaining_after} `!benchmark code def=…` "
                    "blocks still contain `sorry`. Agent left work undone."
                ),
                output_files=impl_files,
                human_review_required=True,
                human_review_instructions=(
                    "Re-run with `--stage python_curate --force` to continue "
                    "filling, or `--continue` to resume the session."
                ),
                session_id=session_id or "",
            )

        # Manifest round-trip: every required top-level key present, every
        # listed module has a real Spec/<Module>.lean stub on disk. Required
        # because the agent has been observed to leave manifest.json as `{}`
        # (or with only a partial set of keys) when it ran out of turn budget,
        # and lake build is happy to ignore an empty manifest. Without this
        # check the validate stage downstream surfaces the gap as a flood of
        # `manifest_schema: missing required …` errors.
        manifest_check_error = _verify_manifest_and_specs(project_dir)
        if manifest_check_error is not None:
            return StageResult(
                stage=self.name,
                success=False,
                error=manifest_check_error,
                output_files=all_files,
                human_review_required=True,
                human_review_instructions=(
                    "Re-run with `--stage python_curate --force` so the agent "
                    "can fill manifest.json and the missing Spec stubs."
                ),
                session_id=session_id or "",
            )

        return StageResult(
            stage=self.name,
            success=True,
            output_files=all_files,
            human_review_required=True,
            human_review_instructions=(
                f"Curation landed at {project_dir}. Inspect a sample, then "
                "(when ready) run `--stage spec_write` to author specs."
            ),
            session_id=session_id or "",
        )


def _verify_manifest_and_specs(project_dir: Path) -> str | None:
    """Return an error message if the manifest is missing required keys or
    a declared spec file does not exist on disk; return ``None`` otherwise.

    Mirrors the validate-stage's ``manifest_schema`` rule but at curate-time
    so the agent fails fast rather than letting a half-finished tree slip
    through to the downstream validate stage. Required top-level keys come
    from ``reference/BankLedger/manifest.json`` (the ratified shape).
    """
    import json as _json

    manifest_path = project_dir / "manifest.json"
    if not manifest_path.exists():
        return f"manifest.json not found at {manifest_path}"
    try:
        manifest = _json.loads(manifest_path.read_text(encoding="utf-8"))
    except (OSError, _json.JSONDecodeError) as e:
        return f"manifest.json is not valid JSON: {e}"

    required_top = {
        "benchmark_id",
        "lean_version",
        "modes_supported",
        "source",
        "curation",
        "files",
        "root_package",
        "packages",
    }
    missing_top = sorted(required_top - manifest.keys())
    if missing_top:
        return "manifest.json missing required top-level keys: " + ", ".join(
            missing_top
        )

    files = manifest.get("files", {})
    required_files = {"root_hub", "harness", "test", "lakefile"}
    missing_files = sorted(required_files - files.keys())
    if missing_files:
        return "manifest.json::files missing required keys: " + ", ".join(missing_files)

    packages = manifest.get("packages", [])
    if not packages or not isinstance(packages, list):
        return "manifest.json::packages must be a non-empty array"

    # Every declared module must have a Spec/<Module>.lean on disk (even if
    # it's just a namespace + placeholder comment — spec_write fills later).
    for pkg in packages:
        for mod in pkg.get("modules", []):
            spec_rel = mod.get("spec")
            if not spec_rel:
                return (
                    f"manifest.json: module {mod.get('name', '?')!r} has no `spec` path"
                )
            spec_path = project_dir / spec_rel
            if not spec_path.exists():
                return (
                    f"manifest.json: declared spec file does not exist on "
                    f"disk: {spec_rel}"
                )
    return None
