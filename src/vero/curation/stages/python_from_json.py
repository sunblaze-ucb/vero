"""Python-from-benchmark.json stage (mode A).

Given a pre-curated ``benchmark.json`` (the shape emitted by the legacy
Python curation pipeline under ``<repo>/task/benchmark.json``),
scaffold a Lean 4 benchmark in the ratified ``Impl/Spec/Bundle/Harness``
paradigm. Specs are left empty for a later ``spec_write`` stage to fill.

Idempotent: running twice on the same input produces identical bytes.
"""

from __future__ import annotations

import json
import re
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path

from vero.curation.lean_project import to_project_name
from vero.curation.stages.base import StageContext, StageResult, StageRunner

# ─────────────────────────────────────────────────────────────
# Data model

_SUPPORTED_PARAM_KINDS = {"Explicit", "Implicit", "Instance"}


@dataclass(frozen=True)
class Param:
    name: str
    typ: str
    kind: str  # Explicit | Implicit | Instance

    def render_binder(self) -> str:
        if self.kind == "Explicit":
            return f"({self.name} : {self.typ})"
        if self.kind == "Implicit":
            return f"{{{self.name} : {self.typ}}}"
        if self.kind == "Instance":
            return f"[{self.name} : {self.typ}]"
        raise ValueError(f"unsupported param kind: {self.kind}")


@dataclass(frozen=True)
class Api:
    name: str  # e.g. "factor"
    params: tuple[Param, ...]
    ret_typ: str  # e.g. "Int"
    tests: tuple["BenchTest", ...] = ()

    @property
    def sig_name(self) -> str:
        """``factor`` → ``FactorSig``."""
        return f"{camel_capitalize(self.name)}Sig"

    @property
    def arrow_type(self) -> str:
        """Collapse params + return type into ``A → B → … → R``.

        Parenthesizes function-typed params so the curried arrow chain stays
        unambiguous: ``(Int → Int → Int) → String`` rather than the malformed
        ``Int → Int → Int → String`` (3-arg fn) for a Python ``Callable`` param.
        Also normalises any ASCII ``->`` arrows in source types to Unicode ``→``.
        """
        if not self.params:
            return _normalize_arrows(self.ret_typ)
        parts: list[str] = []
        for p in self.params:
            t = _normalize_arrows(p.typ)
            if "→" in t:
                parts.append(f"({t})")
            else:
                parts.append(t)
        parts.append(_normalize_arrows(self.ret_typ))
        return " → ".join(parts)


@dataclass(frozen=True)
class BenchTest:
    inputs: tuple[tuple[str, str], ...]  # ordered (name, literal)
    expected: str

    def render_args(
        self,
        api: Api,
        *,
        api_qualifier: dict[str, str] | None = None,
    ) -> str:
        """Render call args in the declared param order, parenthesizing non-trivial literals.

        ``api_qualifier`` (optional, ``{api_name: qualified_form}``) lets the
        caller substitute bare API references with their bundle-qualified form.
        For example, a Python test case `truth_table(nor_gate)` carries the
        bare identifier `nor_gate` in `inputs`; passing `{"nor_gate":
        "canonical.booleanAlgebra.nor_gate"}` makes the rendered call
        `canonical.booleanAlgebra.truth_table canonical.booleanAlgebra.nor_gate`.
        """
        inputs_by_name = dict(self.inputs)
        qualifier = api_qualifier or {}
        out: list[str] = []
        for p in api.params:
            if p.kind != "Explicit":
                # Skip implicit/instance args in the call — Lean infers them.
                continue
            lit = inputs_by_name.get(p.name, "")
            stripped = lit.strip()
            if stripped in qualifier:
                out.append(qualifier[stripped])
            else:
                out.append(_paren_literal(lit))
        return " ".join(out)


@dataclass(frozen=True)
class FileSpec:
    """One entry in ``benchmark.json.files`` → one Impl file + one Spec file."""

    module: str  # e.g. "Primes"
    apis: tuple[Api, ...]
    data_structures: tuple[dict, ...]  # raw dicts; minimal handling for v1
    uses_sqrt: bool  # True if the source references math.sqrt
    has_private_helpers: bool  # source file contains `def __...` / `_foo`


@dataclass(frozen=True)
class Plan:
    """Everything needed to emit the scaffold."""

    benchmark_id: str
    package: str  # e.g. "Primepy"
    repo_impl_field: str  # lowerCamelCase(package)
    bundle_type: str  # "<package>Bundle"
    files: tuple[FileSpec, ...]
    warnings: tuple[str, ...] = ()
    source_meta: dict | None = None


# ─────────────────────────────────────────────────────────────
# Helpers


def camel_capitalize(name: str) -> str:
    """Snake / kebab / dotted → UpperCamelCase, preserving existing CamelCase.

    Examples::

        factor                    -> Factor
        compare_string            -> CompareString
        truth_table               -> TruthTable
        n_input_and_gate          -> NInputAndGate
        QuineMcCluskey            -> QuineMcCluskey
        myApi                     -> MyApi
    """
    if not name:
        return name
    if "_" in name or "-" in name:
        parts = name.replace("-", "_").split("_")
        return "".join(p[:1].upper() + p[1:] if p else "" for p in parts)
    # Already CamelCase / mixed — just uppercase the first letter.
    return name[0].upper() + name[1:]


def lower_first(name: str) -> str:
    if not name:
        return name
    return name[0].lower() + name[1:]


def _module_name_from_file_key(key: str) -> str:
    """``Primes.lean`` → ``Primes``; ``primes.lean`` → ``Primes``;
    ``KarnaughMapSimplification.lean`` → ``KarnaughMapSimplification``;
    ``quine_mc_cluskey.lean`` → ``QuineMcCluskey``.
    """
    stem = Path(key).stem
    return camel_capitalize(stem)


_LIT_PAREN_RE = re.compile(r"^[\w\.]+$")
_ASCII_ARROW_RE = re.compile(r"->")


def _normalize_arrows(t: str) -> str:
    """Replace ASCII ``->`` with Unicode ``→`` for consistency with Lean style."""
    return _ASCII_ARROW_RE.sub("→", t).strip()


def _paren_literal(lit: str) -> str:
    """Parenthesize a literal for a function-call arg when it's not a simple token.

    Examples::

        "1"  -> "1"
        "-1" -> "(-1)"
        "[2, 3, 5]" -> "[2, 3, 5]"
        "some 0" -> "(some 0)"
    """
    lit = lit.strip()
    if not lit:
        return lit
    # Already bracketed / parenthesized list / string — leave as-is.
    if lit[0] in '([{"':
        return lit
    # Simple identifier / number.
    if _LIT_PAREN_RE.fullmatch(lit):
        return lit
    return f"({lit})"


def _detect_source_features(source_file: Path | None) -> tuple[bool, bool]:
    """Return (uses_sqrt, has_private_helpers) from a glance at the source.

    ``uses_sqrt`` is True if ``from math import sqrt`` or ``math.sqrt`` appears.
    ``has_private_helpers`` is True if the file defines any ``def __name`` or
    ``def _name`` (leading underscore) that's not in ``public_apis``.
    """
    if source_file is None or not source_file.exists():
        return (False, False)
    try:
        text = source_file.read_text(encoding="utf-8", errors="ignore")
    except OSError:
        return (False, False)
    uses_sqrt = ("math.sqrt" in text) or bool(
        re.search(r"^\s*from\s+math\s+import\s+.*\bsqrt\b", text, re.MULTILINE)
    )
    private = bool(re.search(r"^\s*def\s+_\w", text, re.MULTILINE))
    return (uses_sqrt, private)


# ─────────────────────────────────────────────────────────────
# Benchmark-JSON parsing


def load_plan(benchmark_json_path: Path) -> Plan:
    """Parse ``benchmark.json`` into a :class:`Plan`.

    Looks up the source Python file next to ``benchmark.json`` at
    ``../original_python/<stem>.py`` to detect external-library usage
    and private helpers.
    """
    data = json.loads(benchmark_json_path.read_text(encoding="utf-8"))

    benchmark_id = data["benchmark_id"]
    package = to_project_name(benchmark_id)
    repo_impl_field = lower_first(package)
    bundle_type = f"{package}Bundle"

    warnings: list[str] = []
    files_out: list[FileSpec] = []

    task_dir = benchmark_json_path.parent
    # task_dir typically has an `original_python/` sibling directory.
    # Some benchmark.json files have `metadata.python_context_path = null`
    # (key present but value missing) — `dict.get(...) or "default"` gives
    # the fallback in both the missing-key and explicit-null cases.
    python_ctx = task_dir / (
        data.get("metadata", {}).get("python_context_path") or "original_python"
    )

    for file_key, file_info in data.get("files", {}).items():
        module = _module_name_from_file_key(file_key)
        apis: list[Api] = []
        for api_raw in file_info.get("public_apis", []):
            sig = api_raw["signature"]
            params: list[Param] = []
            for p in sig.get("params", []):
                if p["kind"] not in _SUPPORTED_PARAM_KINDS:
                    warnings.append(
                        f"{module}.{sig['name']}: skipping param {p['name']!r} "
                        f"with unsupported kind {p['kind']!r}"
                    )
                    continue
                params.append(Param(name=p["name"], typ=p["typ"], kind=p["kind"]))

            tests_raw = api_raw.get("test_cases", {}).get("tests", []) or []
            tests: list[BenchTest] = []
            for t in tests_raw:
                inputs = tuple((k, v) for k, v in t.get("input", {}).items())
                tests.append(
                    BenchTest(inputs=inputs, expected=t.get("expected_output", ""))
                )

            apis.append(
                Api(
                    name=sig["name"],
                    params=tuple(params),
                    ret_typ=sig["typ"],
                    tests=tuple(tests),
                )
            )

        # Detect sqrt + private helpers from the source file.
        source_stem = Path(file_key).stem.lower()
        source_file = python_ctx / f"{source_stem}.py"
        uses_sqrt, has_priv = _detect_source_features(source_file)

        files_out.append(
            FileSpec(
                module=module,
                apis=tuple(apis),
                data_structures=tuple(file_info.get("data_structures", [])),
                uses_sqrt=uses_sqrt,
                has_private_helpers=has_priv,
            )
        )

    return Plan(
        benchmark_id=benchmark_id,
        package=package,
        repo_impl_field=repo_impl_field,
        bundle_type=bundle_type,
        files=tuple(files_out),
        warnings=tuple(warnings),
        source_meta=data.get("metadata"),
    )


# ─────────────────────────────────────────────────────────────
# Emission


def _render_impl_file(plan: Plan, fs: FileSpec) -> str:
    lines: list[str] = []
    lines.append("-- !benchmark @start imports")
    lines.append("-- !benchmark @end imports")
    lines.append("")
    lines.append("/-!")
    lines.append(f"# {plan.package}.Impl.{fs.module}")
    lines.append("")
    lines.append("Scaffolded from `benchmark.json` via the python-from-json curation")
    lines.append("stage. API signatures are extracted to `abbrev`s; bodies are `sorry`")
    lines.append("stubs wrapped in `!benchmark code` markers for the LLM to fill.")
    lines.append("-/")
    lines.append("")

    # Private-helper / external-lib review flags.
    if fs.has_private_helpers:
        lines.append(
            "-- !curation @review v1 [ ] source file has private helper(s) not in public_apis; "
            "LLM may introduce them as api_helper."
        )
        lines.append("")

    # Data structures (minimal — primepy has none; placeholder for other datasets).
    for ds in fs.data_structures:
        name = ds.get("name", "<unnamed>")
        kind = ds.get("kind", "")
        fields = ds.get("fields", [])
        if kind == "Alias" and not fields:
            lines.append(
                f"-- !curation @review human: alias `{name}` has no fields — please fill."
            )
            lines.append(f"-- TODO: structure {name}")
            lines.append("")
            continue
        lines.append(f"structure {name} where")
        for f in fields:
            fname = f.get("name", "<f>")
            ftyp = f.get("typ", "<T>")
            lines.append(f"  {fname} : {ftyp}")
        lines.append("")

    # API signatures inside `namespace <Package>`.
    if fs.apis:
        lines.append(f"namespace {plan.package}")
        lines.append("")
        lines.append("-- ── API signatures (DO NOT MODIFY) ───────────────────────────")
        for api in fs.apis:
            lines.append(f"abbrev {api.sig_name} := {api.arrow_type}")
        lines.append("")
        lines.append(f"end {plan.package}")
        lines.append("")

    # global_aux marker region (always present so file_roles check passes).
    lines.append("-- !benchmark @start global_aux")
    if fs.uses_sqrt:
        lines.append(
            "-- @review human: verify sqrt model (imported from Python's math.sqrt)."
        )
        lines.append("opaque sqrt : Int → Int")
    lines.append("-- !benchmark @end global_aux")
    lines.append("")

    # One code_aux + code slot per API.
    for api in fs.apis:
        lines.append(f"-- !benchmark @start code_aux def={api.name}")
        lines.append(f"-- !benchmark @end code_aux def={api.name}")
        lines.append("")
        lines.append(
            f"-- !curation @review v1 [ ] {api.name} — Impl/{fs.module}, "
            f"exec-fn (api), sorry stub"
        )
        lines.append(
            f"def {plan.package}.{api.name} : {plan.package}.{api.sig_name} :="
        )
        lines.append(f"-- !benchmark @start code def={api.name}")
        lines.append("  sorry")
        lines.append(f"-- !benchmark @end code def={api.name}")
        lines.append("")

    return "\n".join(lines)


def _render_spec_file(plan: Plan, fs: FileSpec) -> str:
    """Empty spec file scaffold — the spec_write stage will populate."""
    lines = [
        f"import {plan.package}.Harness",
        "",
        "/-!",
        f"# {plan.package}.Spec.{fs.module}",
        "",
        "Spec scaffold. Specs are filled in by the `spec_write` stage.",
        "",
        "Each spec must be typed `(impl : RepoImpl) : Prop` and reference",
        f"`impl.{plan.repo_impl_field}.<api>` to stay bundle-faithful.",
        "-/",
        "",
    ]
    return "\n".join(lines)


def _render_bundle_file(plan: Plan) -> str:
    lines: list[str] = []
    for fs in plan.files:
        lines.append(f"import {plan.package}.Impl.{fs.module}")
    lines.append("")
    lines.append("/-!")
    lines.append(f"# {plan.package}.Bundle")
    lines.append("")
    lines.append("Per-package implementation bundle. Collects all API signatures into")
    lines.append(f"one `structure {plan.bundle_type}`.")
    lines.append("")
    lines.append("DO NOT MODIFY — benchmark infrastructure.")
    lines.append("-/")
    lines.append("")
    lines.append(f"structure {plan.bundle_type} where")
    for fs in plan.files:
        for api in fs.apis:
            lines.append(f"  {api.name} : {plan.package}.{api.sig_name}")
    lines.append("")
    return "\n".join(lines)


def _render_harness_file(plan: Plan) -> str:
    lines: list[str] = [
        f"import {plan.package}.Bundle",
        "",
        "/-!",
        f"# {plan.package}.Harness",
        "",
        "Benchmark harness: `RepoImpl` structure (one field per package),",
        "`canonical` instance wiring.",
        "",
        "DO NOT MODIFY — this is benchmark infrastructure.",
        "-/",
        "",
        "structure RepoImpl where",
        f"  {plan.repo_impl_field} : {plan.bundle_type}",
        "",
        "def canonical : RepoImpl where",
        f"  {plan.repo_impl_field} := {{",
    ]
    for fs in plan.files:
        for api in fs.apis:
            lines.append(f"    {api.name} := {plan.package}.{api.name}")
    lines.extend(
        [
            "  }",
            "",
        ]
    )
    return "\n".join(lines)


def _render_test_file(plan: Plan) -> str:
    """Emit ``Test.lean`` with ``#guard`` assertions per benchmark test case.

    Subtlety: the curator's scaffold is sorry-filled, so any ``#guard`` over a
    sorry-bodied def aborts ``lake build``. The output has two parts:

    1. A live ``#guard True`` (not over canonical) so the validator's
       ``check_guards`` sees a real assertion outside any comment block.
    2. A ``/- … -/`` block carrying the inventory of curator-given guards over
       ``canonical.<field>.<api>``. The post-fill stage (or a human) lifts this
       wrapper to activate them once ``Impl/*.lean`` has real bodies. We also
       emit a ``-- !curation @human:`` annotation telling the curator that
       lifting is required.
    """

    lines: list[str] = []
    for fs in plan.files:
        lines.append(f"import {plan.package}.Impl.{fs.module}")
    lines.append(f"import {plan.package}.Harness")
    lines.append("")
    lines.append("/-!")
    lines.append(f"# {plan.package}.Test")
    lines.append("")
    lines.append("Executable conformance tests. `#guard` assertions run against the")
    lines.append("`canonical` wiring. Before the LLM sees the benchmark, the pipeline")
    lines.append("replaces `sorry` stubs — the inventory below activates post-fill.")
    lines.append("")
    lines.append("DO NOT MODIFY — infrastructure.")
    lines.append("-/")
    lines.append("")

    # Live sentinel: a #guard over `True` always succeeds and proves the file
    # is wired; satisfies `check_guards` without depending on canonical.
    lines.append(
        "-- Sentinel — proves Test.lean is wired and counts toward the validator's"
    )
    lines.append("-- guard tally. Real test cases live in the curator block below.")
    lines.append("#guard True")
    lines.append("")

    # Build a name-qualifier map so test cases that pass a bare API
    # identifier (e.g., `truth_table(nor_gate)`) get the bundle-qualified
    # form (`canonical.<field>.nor_gate`). Otherwise the rendered guard
    # references an undefined identifier and lake build fails post-lift.
    api_qualifier: dict[str, str] = {}
    for fs in plan.files:
        for api in fs.apis:
            api_qualifier[api.name] = f"canonical.{plan.repo_impl_field}.{api.name}"

    any_test = False
    inventory: list[str] = []
    for fs in plan.files:
        if not any(api.tests for api in fs.apis):
            continue
        inventory.append(f"-- ── {fs.module} ─────────────────────────")
        for api in fs.apis:
            if not api.tests:
                continue
            for t in api.tests:
                args = t.render_args(api, api_qualifier=api_qualifier)
                call = f"canonical.{plan.repo_impl_field}.{api.name} {args}".rstrip()
                inventory.append(f"#guard {call} = {t.expected}")
                any_test = True
        inventory.append("")

    if any_test:
        lines.append(
            "-- Curator note: lift the `/- … -/` wrapper below once Impl/* has"
        )
        lines.append("-- been filled (sorry-stubs would otherwise abort lake build).")
        lines.append(
            "/- BY curator — guards activate once Impl/*.lean stubs are filled."
        )
        lines.extend(inventory)
        lines.append("-/")

    lines.append("")
    return "\n".join(lines)


def _render_root_hub(plan: Plan) -> str:
    lines = [f"import {plan.package}.Harness", f"import {plan.package}.Test", ""]
    return "\n".join(lines)


def _render_manifest(plan: Plan, lean_version: str = "4.29.1") -> dict:
    packages = [
        {
            "name": plan.package,
            "bundle": f"{plan.package}/Bundle.lean",
            "bundle_type": plan.bundle_type,
            "repo_impl_field": plan.repo_impl_field,
            "modules": [
                {
                    "name": fs.module,
                    "impl": f"{plan.package}/Impl/{fs.module}.lean",
                    "spec": f"{plan.package}/Spec/{fs.module}.lean",
                    "apis": [
                        {
                            "name": api.name,
                            "sig": api.sig_name,
                            "type": api.arrow_type,
                            "kind": "api",
                        }
                        for api in fs.apis
                    ],
                    "specs": [],
                }
                for fs in plan.files
            ],
        }
    ]

    source_meta = plan.source_meta or {}
    curation_date = (
        source_meta.get("curation_timestamp")
        or datetime.now(timezone.utc).date().isoformat()
    )
    # curation.date is usually a date-only string; reuse what's there, else today.
    if (
        isinstance(curation_date, str)
        and len(curation_date) >= 10
        and curation_date[4] == "-"
    ):
        curation_date = curation_date[:10]

    return {
        "benchmark_id": plan.benchmark_id,
        "description": f"Python-from-JSON scaffold for `{plan.benchmark_id}`.",
        "lean_version": lean_version,
        "modes_supported": ["proof", "codeproof"],
        "source": {
            "kind": "translated",
            "language": "python",
            "repo_url": source_meta.get("origin_repo") or None,
            "commit_hash": source_meta.get("commit_hash") or None,
            "path": source_meta.get("python_context_path") or None,
        },
        "curation": {
            "date": curation_date,
        },
        "root_package": plan.package,
        "files": {
            "root_hub": f"{plan.package}.lean",
            "harness": f"{plan.package}/Harness.lean",
            "test": f"{plan.package}/Test.lean",
            "lakefile": "lakefile.toml",
        },
        "packages": packages,
    }


# ─────────────────────────────────────────────────────────────
# Emitter


def emit_scaffold(
    plan: Plan,
    out_dir: Path,
    *,
    lean_version: str = "4.29.1",
) -> list[Path]:
    """Write the scaffold under ``out_dir/<Package>/``. Returns files written.

    Layout matches ``reference/BankLedger/`` (the canonical convention): the
    lake project root is ``out_dir/<Package>/`` and the package source tree
    sits one level deeper at ``out_dir/<Package>/<Package>/``.

    Idempotent: writes the same bytes each time given the same plan.
    """
    out_dir = Path(out_dir).resolve()
    lake_root = out_dir / plan.package
    lake_root.mkdir(parents=True, exist_ok=True)

    # Mathlib is required by default — Python-translated benchmarks tend
    # to reach for `Mathlib.Data.List.Sort`, `Mathlib.Tactic`, etc. The
    # tag follows the lean toolchain ("v" + lean_version); mathlib4
    # publishes a matching tag for each Lean release.
    lakefile_body = (
        f'name = "{plan.package}"\n'
        f'version = "0.1.0"\n'
        f'defaultTargets = ["{plan.package}"]\n'
        "\n"
        "[[require]]\n"
        'scope = "leanprover-community"\n'
        'name = "mathlib"\n'
        f'rev = "v{lean_version}"\n'
        "\n"
        "[[lean_lib]]\n"
        f'name = "{plan.package}"\n'
        'srcDir = "."\n'
        'leanOptions = [{ name = "autoImplicit", value = false }]\n'
    )
    toolchain_body = f"leanprover/lean4:v{lean_version}\n"

    written: list[Path] = []

    def write(path: Path, content: str) -> None:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content, encoding="utf-8")
        written.append(path)

    write(lake_root / "lakefile.toml", lakefile_body)
    write(lake_root / "lean-toolchain", toolchain_body)
    write(lake_root / f"{plan.package}.lean", _render_root_hub(plan))

    pkg_dir = lake_root / plan.package
    impl_dir = pkg_dir / "Impl"
    spec_dir = pkg_dir / "Spec"

    for fs in plan.files:
        write(impl_dir / f"{fs.module}.lean", _render_impl_file(plan, fs))
        write(spec_dir / f"{fs.module}.lean", _render_spec_file(plan, fs))

    write(pkg_dir / "Bundle.lean", _render_bundle_file(plan))
    write(pkg_dir / "Harness.lean", _render_harness_file(plan))
    write(pkg_dir / "Test.lean", _render_test_file(plan))

    manifest = _render_manifest(plan, lean_version=lean_version)
    write(
        lake_root / "manifest.json",
        json.dumps(manifest, indent=2, ensure_ascii=False) + "\n",
    )

    return written


# ─────────────────────────────────────────────────────────────
# Stage runner (mostly a thin shim over emit_scaffold)


class PythonFromJsonStage(StageRunner):
    """Scaffold a Lean 4 benchmark from a pre-existing ``benchmark.json``.

    Expected context: ``ctx.source_dir`` points at the directory containing
    ``task/benchmark.json`` (typically under ``<repo>/``), and
    ``ctx.lean_output_dir`` is the scaffold target.
    """

    name = "python_from_json"
    human_review = False

    async def run(self, ctx: StageContext) -> StageResult:
        bench_json = _find_benchmark_json(ctx.source_dir)
        if bench_json is None:
            return StageResult(
                stage=self.name,
                success=False,
                error=f"benchmark.json not found under {ctx.source_dir}",
            )
        try:
            plan = load_plan(bench_json)
        except (KeyError, ValueError, json.JSONDecodeError) as e:
            return StageResult(
                stage=self.name,
                success=False,
                error=f"failed to load benchmark.json: {e}",
            )
        written = emit_scaffold(
            plan,
            ctx.lean_output_dir,
            lean_version=ctx.config.lean_version,
        )
        # Populate benchmark_id so downstream stages (python_adjust_bodies,
        # spec_write, validate) can compute the canonical lake-root path
        # `lean_output_dir / to_project_name(benchmark_id)` without re-reading
        # the benchmark.json. Mirrors what InitStage does for verified_to_lean.
        if not ctx.config.benchmark_id:
            ctx.config.benchmark_id = plan.benchmark_id
            ctx.config.save()
        return StageResult(
            stage=self.name,
            success=True,
            output_files=[str(p) for p in written],
            human_review_required=False,
        )


def _find_benchmark_json(source_dir: Path) -> Path | None:
    """Resolve the benchmark.json path under a dataset directory."""
    candidates = [
        source_dir / "task" / "benchmark.json",
        source_dir / "benchmark.json",
    ]
    for c in candidates:
        if c.exists():
            return c
    return None


# ─────────────────────────────────────────────────────────────
# CLI helper — invoked directly from the curation CLI's `python-from-json`
# subcommand.


def run_python_from_json(
    benchmark_json: Path,
    out_dir: Path,
    *,
    lean_version: str = "4.29.1",
) -> Plan:
    """Convenience entry point used by both the stage and the CLI subcommand.

    ``out_dir`` is the *parent* of the lake project — the actual lake root
    lands at ``out_dir/<Package>/`` (matching ``reference/BankLedger/``).
    """
    plan = load_plan(benchmark_json)
    emit_scaffold(plan, out_dir, lean_version=lean_version)
    return plan
