"""Rule-based validation checks for curated Lean 4 benchmarks.

Reference: docs/pipeline-schema.md (validate.json section).
"""

from __future__ import annotations

import json
import re
import subprocess
from pathlib import Path
from typing import Any

import yaml

from .markers import BENCHMARK_KEYS, pair_slots, parse_file_markers
from .types import CheckResult, Finding

# ─────────────────────────────────────────────────────────────
# Helpers


def _load_manifest(benchmark: Path) -> tuple[dict | None, list[Finding]]:
    """Load manifest.json. Returns (manifest, errors)."""
    path = benchmark / "manifest.json"
    if not path.exists():
        return None, [Finding("error", f"manifest.json not found at {path}")]
    try:
        return json.loads(path.read_text()), []
    except json.JSONDecodeError as e:
        return None, [Finding("error", f"manifest.json is not valid JSON: {e}")]


def _abs(benchmark: Path, relpath: str) -> Path:
    return benchmark / relpath


def _workspace_candidates(benchmark: Path) -> list[Path]:
    """Likely workspace roots for sidecar curation artifacts.

    Curated outputs seen in the wild use both of these shapes:

    - <workspace>/.vero/plan.json and <workspace>/lean_output/<Project>/
    - <workspace>/curation/selection_plan.json and
      <workspace>/lean_output/<Project>/
    """
    out = [benchmark, benchmark.parent, benchmark.parent.parent]
    return list(dict.fromkeys(p for p in out if p))


def _json_candidates(benchmark: Path, names: list[str]) -> list[Path]:
    out: list[Path] = []
    for root in _workspace_candidates(benchmark):
        for name in names:
            out.append(root / name)
            out.append(root / ".vero" / name)
            out.append(root / "curation" / name)
    return list(dict.fromkeys(out))


def _load_first_json(
    benchmark: Path, names: list[str]
) -> tuple[dict | None, Path | None, list[Finding]]:
    for path in _json_candidates(benchmark, names):
        if not path.exists():
            continue
        try:
            return json.loads(path.read_text(encoding="utf-8")), path, []
        except json.JSONDecodeError as e:
            return None, path, [Finding("error", f"{path} is not valid JSON: {e}")]
    return None, None, []


def _find_config_yaml(benchmark: Path) -> Path | None:
    for root in _workspace_candidates(benchmark):
        candidate = root / "config.yaml"
        if candidate.exists():
            return candidate
    return None


def _normalize_name(name: str) -> str:
    return name.rsplit(".", 1)[-1]


_ALLOWED_ENTITY_ROLES = frozenset(
    {
        "unclassified",
        "scored_api",
        "scored_spec",
        "api_helper",
        "semantic_model",
        "spec_helper",
        "trusted_theory",
        "trusted_external",
        "proof_helper_task",
        "trusted_theorem",
        "reference_api",
        "dropped_with_reason",
        "requires_human_review",
    }
)
_ALLOWED_DISPOSITIONS = frozenset(
    {"unclassified", "provided", "scored", "hidden", "dropped", "axiomatized", "opaque"}
)


def _iter_manifest_modules(manifest: dict) -> Any:
    for pkg in manifest.get("packages", []):
        for mod in pkg.get("modules", []):
            yield pkg, mod


def _manifest_api_entries(manifest: dict) -> list[tuple[dict, dict, dict]]:
    entries = []
    for pkg, mod in _iter_manifest_modules(manifest):
        for api in mod.get("apis", []):
            entries.append((pkg, mod, api))
        for api in mod.get("api_helpers", []):
            helper = dict(api) if isinstance(api, dict) else {"name": api}
            helper.setdefault("kind", "api_helper")
            entries.append((pkg, mod, helper))
    return entries


def _manifest_spec_entries(manifest: dict) -> list[tuple[dict, dict, dict]]:
    entries = []
    for pkg, mod in _iter_manifest_modules(manifest):
        for spec in mod.get("specs", []):
            item = dict(spec) if isinstance(spec, dict) else {"name": spec}
            item.setdefault("kind", "spec")
            entries.append((pkg, mod, item))
        for helper in mod.get("spec_helpers", []):
            item = dict(helper) if isinstance(helper, dict) else {"name": helper}
            item.setdefault("kind", "spec_helper")
            entries.append((pkg, mod, item))
    return entries


def _manifest_spec_name(spec: object) -> str | None:
    if isinstance(spec, dict):
        name = spec.get("name")
        return name if isinstance(name, str) else None
    return spec if isinstance(spec, str) else None


def _source_path_variants(value: object) -> set[str]:
    """Comparable relative suffixes for source paths from different sidecars."""
    if not isinstance(value, str) or not value:
        return set()
    normalized = value.replace("\\", "/").strip("/")
    parts = [part for part in normalized.split("/") if part and part != "."]
    return {"/".join(parts[i:]) for i in range(len(parts))}


def _collect_source_ref_ids(node: object) -> set[str]:
    refs: set[str] = set()

    def visit(value: object) -> None:
        if isinstance(value, dict):
            for key in (
                "source_id",
                "stable_source_id",
                "source_theorem",
                "source_spec",
            ):
                ref = value.get(key)
                if (
                    isinstance(ref, str)
                    and ":" in ref
                    and not ref.startswith("baseline:")
                    and not ref.startswith("planner:")
                ):
                    refs.add(ref)
            for key in ("source_ids", "source_theorems", "source_specs"):
                raw = value.get(key)
                if isinstance(raw, list):
                    for ref in raw:
                        if (
                            isinstance(ref, str)
                            and ":" in ref
                            and not ref.startswith("baseline:")
                            and not ref.startswith("planner:")
                        ):
                            refs.add(ref)
            for child in value.values():
                visit(child)
        elif isinstance(value, list):
            for child in value:
                visit(child)

    visit(node)
    return refs


def _collect_decl_names(node: object) -> set[str]:
    names: set[str] = set()

    def visit(value: object) -> None:
        if isinstance(value, dict):
            for key in (
                "name",
                "lean_name",
                "target_name",
                "upstream_name",
                "qualified_name",
            ):
                name = value.get(key)
                if isinstance(name, str) and name:
                    names.add(name)
                    names.add(name.rsplit(".", 1)[-1])
            for child in value.values():
                visit(child)
        elif isinstance(value, list):
            for child in value:
                visit(child)

    visit(node)
    return names


def _strip_line_comments(text: str) -> str:
    return "\n".join(line.split("--", 1)[0] for line in text.splitlines())


def _is_python_scaffold(manifest: dict) -> bool:
    source = manifest.get("source", {})
    return isinstance(source, dict) and source.get("language") == "python"


# ─────────────────────────────────────────────────────────────
# Check 1: manifest schema valid


_REQUIRED_TOP_KEYS = {
    "benchmark_id",
    "lean_version",
    "modes_supported",
    "source",
    "curation",
    "files",
    "packages",
    "root_package",
}
_REQUIRED_FILES_KEYS = {"root_hub", "harness", "test", "lakefile"}


def check_manifest_schema(benchmark: Path) -> CheckResult:
    """Check 1: manifest.json is valid JSON and has the required fields."""
    manifest, errors = _load_manifest(benchmark)
    if manifest is None:
        return CheckResult("manifest_schema", "fail", errors)

    details: list[Finding] = []
    missing = _REQUIRED_TOP_KEYS - set(manifest.keys())
    for k in sorted(missing):
        details.append(Finding("error", f"missing required top-level key: {k}"))

    files = manifest.get("files", {})
    if not isinstance(files, dict):
        details.append(Finding("error", "`files` must be an object"))
    else:
        missing = _REQUIRED_FILES_KEYS - set(files.keys())
        for k in sorted(missing):
            details.append(Finding("error", f"missing required files.{k}"))

    packages = manifest.get("packages")
    if not isinstance(packages, list) or not packages:
        details.append(Finding("error", "`packages` must be a non-empty array"))
    else:
        root_name = manifest.get("root_package")
        if root_name not in {p.get("name") for p in packages}:
            details.append(
                Finding(
                    "error",
                    f"root_package={root_name!r} does not match any packages[].name",
                )
            )
        for i, pkg in enumerate(packages):
            for k in ("name", "bundle", "bundle_type", "repo_impl_field", "modules"):
                if k not in pkg:
                    details.append(
                        Finding(
                            "error",
                            f"packages[{i}] missing required field {k!r}",
                        )
                    )
            for j, mod in enumerate(pkg.get("modules", [])):
                for k in ("name", "impl", "spec", "apis", "specs"):
                    if k not in mod:
                        details.append(
                            Finding(
                                "error",
                                f"packages[{i}].modules[{j}] missing {k!r}",
                            )
                        )

    status = "fail" if any(f.severity == "error" for f in details) else "pass"
    return CheckResult("manifest_schema", status, details)


# ─────────────────────────────────────────────────────────────
# Check 2: manifest-vs-code consistency


# Optional def-modifiers Lean accepts before `def`. Lean→Lean curation
# preserves source modifiers (e.g. `noncomputable def`, `partial def`)
# verbatim, so the validator must tolerate them in front of the def.
_DEF_MOD = r"(?:(?:noncomputable|partial|private|protected|unsafe)\s+)*"

_ABBREV_SIG_RE = re.compile(r"^\s*abbrev\s+(\w+)\s*:?.*?:=\s*(.+?)\s*$")
_ABBREV_MULTILINE_RE = re.compile(
    r"^\s*abbrev\s+(\w+)\s*:?[^:=]*?:=\s*([\s\S]*?)(?=\n\s*(?:abbrev|def|theorem|instance|structure|inductive|@\[|--|/-|namespace|end\b|/--|\Z)|\Z)",
    re.MULTILINE,
)
# Multi-line variant: `def Name :\n   SigType :=` — common for long sigs.
_DEF_FN_MULTILINE_RE = re.compile(
    rf"^\s*{_DEF_MOD}def\s+(\S+)(?:\s+(?:\([^)]*\)|\{{[^}}]*\}}|\[[^\]]*\]))*\s*:\s*([\s\S]+?)\s*:=",
    re.MULTILINE,
)
# Lean 4 identifiers may contain `?` and `!` (besides `\w`). Spec names
# extracted from source theorems sometimes carry those (e.g.
# `spec_matches_lt_next?_some`).
_DEF_SPEC_RE = re.compile(rf"^\s*{_DEF_MOD}def\s+(spec_[\w?!']+)\s*\(")
# Inline-args shape: `def Name (a : T) (b : U) ... : Ret :=`. Used by
# Lean-to-Lean curation where source defs carry args inline rather than via a
# Sig abbrev.
_DEF_FN_INLINE_ARGS_RE = re.compile(
    rf"^\s*{_DEF_MOD}def\s+(\S+)\s*[\(\[\{{]",
    re.MULTILINE,
)
_DEF_NAME_RE = re.compile(rf"^\s*{_DEF_MOD}def\s+(\S+)", re.MULTILINE)
_STRUCTURE_RE = re.compile(r"^\s*structure\s+(\w+)\s+where")
_FIELD_IN_STRUCTURE_RE = re.compile(r"^\s+(\w+)\s*:\s*(\S+)")
_DEF_CANONICAL_RE = re.compile(rf"^\s*{_DEF_MOD}def\s+canonical\b", re.MULTILINE)


def _manifest_name_set(items: list) -> set[str]:
    """Collect manifest entry names from either string or object entries."""
    names: set[str] = set()
    for item in items:
        if isinstance(item, str):
            names.add(item)
        elif isinstance(item, dict) and item.get("name"):
            names.add(item["name"])
    return names


def _collect_abbrevs(text: str) -> dict[str, str]:
    """Return {abbrev_name: rhs} for top-level abbrevs. Supports multiline rhs.

    Normalizes whitespace so a signature split across lines compares equal to the
    same signature on one line (enabling manifest `type` field equality checks).
    """
    out: dict[str, str] = {}
    for m in _ABBREV_MULTILINE_RE.finditer(text):
        name, rhs = m.group(1), m.group(2)
        out[name] = re.sub(r"\s+", " ", rhs).strip()
    return out


def _collect_fn_defs(text: str) -> dict[str, str]:
    """Return {fn_name_without_ns: sig_type}. Strips leading namespace.

    Handles two shapes:
      def Ns.name : <sig> := ...
      def Ns.name :\n    <multi-line sig> :=
    """
    out: dict[str, str] = {}
    # Pass 1: multi-line `def Name :\n <sig> :=` (run first since it subsumes single-line)
    for m in _DEF_FN_MULTILINE_RE.finditer(text):
        name = m.group(1)
        sig = re.sub(r"\s+", " ", m.group(2)).strip()
        tail = name.rsplit(".", 1)[-1]
        out[tail] = sig
    # Fallback for pattern-matching definitions without `:=`, e.g.
    # `def foo : T | ctor => ...`. The validator primarily needs to know that
    # manifest-listed defs exist; type equality remains best-effort above.
    for m in _DEF_NAME_RE.finditer(text):
        name = m.group(1)
        tail = name.rsplit(".", 1)[-1]
        out.setdefault(tail, "")
    return out


def _collect_spec_defs(text: str) -> set[str]:
    return {m.group(1) for line in text.splitlines() if (m := _DEF_SPEC_RE.match(line))}


def _parse_structure_fields(text: str, struct_name: str) -> dict[str, str] | None:
    """Parse a `structure X where` and return {field_name: field_type}, or None if not found."""
    lines = text.splitlines()
    for i, line in enumerate(lines):
        m = _STRUCTURE_RE.match(line)
        if m and m.group(1) == struct_name:
            fields: dict[str, str] = {}
            for j in range(i + 1, len(lines)):
                inner = lines[j]
                if not inner.strip():
                    continue
                if inner and not inner.startswith(" ") and not inner.startswith("\t"):
                    break  # end of structure body
                if fm := _FIELD_IN_STRUCTURE_RE.match(inner):
                    fields[fm.group(1)] = fm.group(2).strip()
                elif inner.startswith("--"):
                    continue
                else:
                    # Non-field line inside structure — stop
                    break
            return fields
    return None


def check_manifest_vs_code(benchmark: Path) -> CheckResult:
    """Check 2: manifest APIs/specs round-trip against Impl/, Spec/, Bundle, Harness."""
    manifest, errors = _load_manifest(benchmark)
    if manifest is None:
        return CheckResult("manifest_vs_code", "fail", errors)

    details: list[Finding] = []

    for pkg in manifest.get("packages", []):
        bundle_rel = pkg.get("bundle")
        bundle_type = pkg.get("bundle_type")
        if bundle_rel:
            bundle_path = _abs(benchmark, bundle_rel)
            if not bundle_path.exists():
                details.append(
                    Finding(
                        "error",
                        f"bundle file not found: {bundle_rel}",
                        location=bundle_rel,
                    )
                )
            elif bundle_type:
                text = bundle_path.read_text()
                if _parse_structure_fields(text, bundle_type) is None:
                    details.append(
                        Finding(
                            "error",
                            f"bundle_type {bundle_type!r} not found as `structure` in {bundle_rel}",
                            location=bundle_rel,
                        )
                    )

        for mod in pkg.get("modules", []):
            impl_rel = mod.get("impl")
            spec_rel = mod.get("spec")
            impl_path = _abs(benchmark, impl_rel) if impl_rel else None
            spec_path = _abs(benchmark, spec_rel) if spec_rel else None

            if impl_path and impl_path.exists():
                impl_text = impl_path.read_text()
                abbrevs = _collect_abbrevs(impl_text)
                fn_defs = _collect_fn_defs(impl_text)
                for api in mod.get("apis", []):
                    kind = api.get("kind", "api")
                    sig = api.get("sig")
                    expected_type = api.get("type", "").strip()
                    name = api.get("name")
                    if kind == "api":
                        if sig and sig not in abbrevs:
                            details.append(
                                Finding(
                                    "error",
                                    f"API sig abbrev {sig!r} not found in {impl_rel}",
                                    location=impl_rel,
                                )
                            )
                        elif sig and expected_type and abbrevs[sig] != expected_type:
                            details.append(
                                Finding(
                                    "warn",
                                    f"sig type mismatch for {sig}: manifest={expected_type!r}, code={abbrevs[sig]!r}",
                                    location=impl_rel,
                                )
                            )
                        # Allow dotted manifest names (`Foo.bar`) — `_collect_fn_defs`
                        # keys the table by the unqualified tail.
                        lookup = name.rsplit(".", 1)[-1] if name else None
                        if lookup and lookup not in fn_defs:
                            details.append(
                                Finding(
                                    "error",
                                    f"API fn def {name!r} not found in {impl_rel}",
                                    location=impl_rel,
                                )
                            )
                    elif kind == "api_helper":
                        if sig is not None:
                            details.append(
                                Finding(
                                    "warn",
                                    f"api_helper {name!r} has sig {sig!r}; helpers "
                                    "are not signature-constrained",
                                    location=impl_rel,
                                )
                            )
                        lookup = name.rsplit(".", 1)[-1] if name else None
                        if lookup and lookup not in fn_defs:
                            details.append(
                                Finding(
                                    "error",
                                    f"api_helper fn def {name!r} not found in {impl_rel}",
                                    location=impl_rel,
                                )
                            )
                    else:
                        details.append(
                            Finding(
                                "error",
                                f"unknown api kind {kind!r} for {name!r} in {impl_rel}",
                                location=impl_rel,
                            )
                        )

                # api_helpers (dedicated list, same shape as apis with kind=api_helper)
                for helper in mod.get("api_helpers", []):
                    name = helper.get("name")
                    if name and name not in fn_defs:
                        details.append(
                            Finding(
                                "error",
                                f"api_helper fn def {name!r} not found in {impl_rel}",
                                location=impl_rel,
                            )
                        )
            elif impl_rel:
                details.append(
                    Finding(
                        "error", f"impl file missing: {impl_rel}", location=impl_rel
                    )
                )

            if spec_path and spec_path.exists():
                spec_names_in_file = _collect_spec_defs(spec_path.read_text())
                for s in mod.get("specs", []):
                    spec_name = _manifest_spec_name(s)
                    if spec_name and spec_name not in spec_names_in_file:
                        details.append(
                            Finding(
                                "error",
                                f"spec def {spec_name!r} not found in {spec_rel}",
                                location=spec_rel,
                            )
                        )
            elif spec_rel:
                details.append(
                    Finding(
                        "error", f"spec file missing: {spec_rel}", location=spec_rel
                    )
                )

    # RepoImpl in Harness.lean has one field per package with matching bundle type
    harness_rel = manifest.get("files", {}).get("harness")
    if harness_rel:
        harness_path = _abs(benchmark, harness_rel)
        if harness_path.exists():
            harness_text = harness_path.read_text()
            repo_impl_fields = _parse_structure_fields(harness_text, "RepoImpl")
            if repo_impl_fields is None:
                details.append(
                    Finding(
                        "error",
                        "structure RepoImpl not found in Harness.lean",
                        location=harness_rel,
                    )
                )
            else:
                expected = {
                    pkg["repo_impl_field"]: pkg["bundle_type"]
                    for pkg in manifest.get("packages", [])
                }
                for field, bundle in expected.items():
                    if field not in repo_impl_fields:
                        details.append(
                            Finding(
                                "error",
                                f"RepoImpl missing field {field!r} : {bundle}",
                                location=harness_rel,
                            )
                        )
                    elif repo_impl_fields[field] != bundle:
                        details.append(
                            Finding(
                                "error",
                                f"RepoImpl.{field} type is {repo_impl_fields[field]!r}, expected {bundle!r}",
                                location=harness_rel,
                            )
                        )
            # canonical exists
            if not _DEF_CANONICAL_RE.search(harness_text):
                details.append(
                    Finding(
                        "error",
                        "`def canonical` not found in Harness.lean",
                        location=harness_rel,
                    )
                )
        else:
            details.append(Finding("error", f"harness file missing: {harness_rel}"))

    status = (
        "fail"
        if any(f.severity == "error" for f in details)
        else ("warn" if details else "pass")
    )
    return CheckResult("manifest_vs_code", status, details)


# ─────────────────────────────────────────────────────────────
# Check 3: marker grammar


_PROOF_KINDS = frozenset({"prove", "disprove", "unsat", "sat", "joint_unsat"})
_CLAIM_KINDS = frozenset({"joint_unsat"})


def _collect_editable_files(benchmark: Path, manifest: dict) -> list[Path]:
    """Files that may carry markers: Impl + Proof (modematerialized) + Joint."""
    out: list[Path] = []
    for pkg in manifest.get("packages", []):
        for mod in pkg.get("modules", []):
            if rel := mod.get("impl"):
                p = _abs(benchmark, rel)
                if p.exists():
                    out.append(p)
    # Proof illustration dirs (if present) are informational but we check them too.
    for pkg in manifest.get("packages", []):
        pkg_dir = benchmark / pkg["name"]
        for illus in ("Proof_modeproof", "Proof_modecodeproof", "Proof"):
            d = pkg_dir / illus
            if d.is_dir():
                out.extend(sorted(d.glob("*.lean")))
    return out


def check_markers_grammar(benchmark: Path) -> CheckResult:
    """Check 3: every !benchmark marker has valid key/fields; !solution grammar OK."""
    manifest, errors = _load_manifest(benchmark)
    if manifest is None:
        return CheckResult("markers_grammar", "fail", errors)

    details: list[Finding] = []

    for path in _collect_editable_files(benchmark, manifest):
        rel = path.relative_to(benchmark)
        markers = parse_file_markers(path)
        pairs, pair_errors = pair_slots(markers)
        for err in pair_errors:
            details.append(Finding("error", err, location=str(rel)))

        for m in markers:
            if m.prefix != "benchmark":
                continue
            if m.key not in BENCHMARK_KEYS:
                details.append(
                    Finding(
                        "error",
                        f"unknown !benchmark key {m.key!r}",
                        location=f"{rel}:{m.line_no}",
                    )
                )
                continue
            if m.boundary == "start":
                # Required def= for keys that need it
                if m.key in ("code", "code_aux", "proof", "proof_aux", "claim"):
                    if "def" not in m.fields:
                        details.append(
                            Finding(
                                "error",
                                f"!benchmark @start {m.key} is missing def=<name>",
                                location=f"{rel}:{m.line_no}",
                            )
                        )
                # Required kind/target for proof and claim
                if m.key == "proof":
                    kind = m.fields.get("kind")
                    if kind not in _PROOF_KINDS:
                        details.append(
                            Finding(
                                "error",
                                f"proof kind={kind!r} not in {sorted(_PROOF_KINDS)}",
                                location=f"{rel}:{m.line_no}",
                            )
                        )
                    if kind != "joint_unsat" and "target" not in m.fields:
                        details.append(
                            Finding(
                                "error",
                                f"proof kind={kind} requires target=<spec_name>",
                                location=f"{rel}:{m.line_no}",
                            )
                        )
                if m.key == "claim":
                    kind = m.fields.get("kind")
                    if kind not in _CLAIM_KINDS:
                        details.append(
                            Finding(
                                "error",
                                f"claim kind={kind!r} not in {sorted(_CLAIM_KINDS)}",
                                location=f"{rel}:{m.line_no}",
                            )
                        )

        # !solution grammar
        for m in markers:
            if m.prefix == "solution" and m.boundary == "start":
                if "def" not in m.fields:
                    details.append(
                        Finding(
                            "error",
                            "!solution @start missing def=<name>",
                            location=f"{rel}:{m.line_no}",
                        )
                    )
                if "kind" not in m.fields:
                    details.append(
                        Finding(
                            "error",
                            "!solution @start missing kind=<kind>",
                            location=f"{rel}:{m.line_no}",
                        )
                    )

        # def= uniqueness within (file, key)
        seen: dict[tuple[str, str | None], int] = {}
        for slot in pairs:
            if slot.prefix != "benchmark":
                continue
            key = (slot.key, slot.def_name)
            if key in seen:
                details.append(
                    Finding(
                        "error",
                        f"duplicate def={slot.def_name} for key={slot.key} "
                        f"(previous at line {seen[key]}, again at line {slot.start_line})",
                        location=str(rel),
                    )
                )
            else:
                seen[key] = slot.start_line

    status = "fail" if any(f.severity == "error" for f in details) else "pass"
    return CheckResult("markers_grammar", status, details)


# ─────────────────────────────────────────────────────────────
# Check 4: marker positioning


_IMPORT_RE = re.compile(r"^\s*import\s+\S")


def check_markers_positioning(benchmark: Path) -> CheckResult:
    """Check 4: imports marker immediately after last import; proof_aux never between `by` and body."""
    manifest, errors = _load_manifest(benchmark)
    if manifest is None:
        return CheckResult("markers_positioning", "fail", errors)

    details: list[Finding] = []
    for path in _collect_editable_files(benchmark, manifest):
        rel = path.relative_to(benchmark)
        lines = path.read_text().splitlines()
        # Find last `import` line (1-based)
        last_import = 0
        for i, line in enumerate(lines, start=1):
            if _IMPORT_RE.match(line):
                last_import = i
        # Find !benchmark @start imports line
        markers = parse_file_markers(path)
        imports_starts = [
            m
            for m in markers
            if m.prefix == "benchmark" and m.boundary == "start" and m.key == "imports"
        ]
        if not imports_starts:
            # Frozen Impl files with no fillable APIs are intentionally
            # marker-free; file_roles enforces that convention. Only files
            # that carry editable markers need an imports marker to position.
            if not markers:
                continue
            details.append(
                Finding(
                    "error",
                    "missing !benchmark @start imports marker",
                    location=str(rel),
                )
            )
            continue
        if len(imports_starts) > 1:
            details.append(
                Finding(
                    "error",
                    f"multiple !benchmark imports markers at lines {[m.line_no for m in imports_starts]}",
                    location=str(rel),
                )
            )
        im = imports_starts[0]
        # Check: between last import line and imports marker, only whitespace/blank lines
        expected_range = range(last_import + 1, im.line_no)
        offenders = [i for i in expected_range if lines[i - 1].strip() != ""]
        if offenders:
            details.append(
                Finding(
                    "error",
                    f"imports marker at line {im.line_no} not adjacent to last import "
                    f"(line {last_import}); intervening non-blank lines: {offenders}",
                    location=f"{rel}:{im.line_no}",
                )
            )

        # proof_aux positioning: must not be between `by` and the proof body tactic
        pairs, _ = pair_slots(markers)
        proof_aux_pairs = [
            p for p in pairs if p.prefix == "benchmark" and p.key == "proof_aux"
        ]
        proof_pairs = [p for p in pairs if p.prefix == "benchmark" and p.key == "proof"]
        for pa in proof_aux_pairs:
            # Find the paired proof slot with same def_name
            paired = next((p for p in proof_pairs if p.def_name == pa.def_name), None)
            if paired is None:
                # Some proof_aux slots are unpaired in illustrations (OK)
                continue
            # proof_aux must be BEFORE proof (file-level); never between `by` and sorry
            if pa.start_line > paired.start_line:
                details.append(
                    Finding(
                        "error",
                        f"proof_aux def={pa.def_name} (line {pa.start_line}) comes AFTER its proof "
                        f"(line {paired.start_line}); should be before the theorem/claim",
                        location=f"{rel}:{pa.start_line}",
                    )
                )

    status = (
        "fail"
        if any(f.severity == "error" for f in details)
        else ("warn" if details else "pass")
    )
    return CheckResult("markers_positioning", status, details)


# ─────────────────────────────────────────────────────────────
# Check 5: file-role completeness


def check_file_roles(benchmark: Path) -> CheckResult:
    """Check 5: Impl files have full marker set; Spec/Harness/Test/root have none."""
    manifest, errors = _load_manifest(benchmark)
    if manifest is None:
        return CheckResult("file_roles", "fail", errors)

    details: list[Finding] = []

    # Impl files: must have imports + global_aux pair, and code+code_aux pair per API.
    # Files with no APIs (pure vocabulary / opaque / axiom modules) need no markers
    # per task0423.md — they're frozen context.
    for pkg in manifest.get("packages", []):
        for mod in pkg.get("modules", []):
            impl_rel = mod.get("impl")
            if not impl_rel:
                continue
            impl_path = _abs(benchmark, impl_rel)
            if not impl_path.exists():
                continue
            fillable_apis = [
                api for api in mod.get("apis", []) if api.get("kind", "api") == "api"
            ]
            markers = parse_file_markers(impl_path)
            pairs, _ = pair_slots(markers)
            keys_present = {
                (p.key, p.def_name) for p in pairs if p.prefix == "benchmark"
            }
            if not fillable_apis:
                # Frozen file (no LLM-fillable APIs): enforce marker-free convention
                # so the agent can't accidentally edit context.
                if markers:
                    details.append(
                        Finding(
                            "warn",
                            f"{impl_rel}: Impl file has no apis but carries "
                            f"{len(markers)} markers (should be marker-free)",
                            location=impl_rel,
                        )
                    )
                continue
            if ("imports", None) not in keys_present:
                details.append(
                    Finding(
                        "error",
                        f"{impl_rel}: missing !benchmark imports slot",
                        location=impl_rel,
                    )
                )
            if ("global_aux", None) not in keys_present:
                details.append(
                    Finding(
                        "error",
                        f"{impl_rel}: missing !benchmark global_aux slot",
                        location=impl_rel,
                    )
                )
            for api in mod.get("apis", []):
                kind = api.get("kind", "api")
                name = api.get("name")
                # api_helpers are free-form: no marker requirement.
                if kind != "api":
                    continue
                if name and ("code", name) not in keys_present:
                    details.append(
                        Finding(
                            "error",
                            f"{impl_rel}: missing !benchmark code slot def={name}",
                            location=impl_rel,
                        )
                    )
                if name and ("code_aux", name) not in keys_present:
                    details.append(
                        Finding(
                            "error",
                            f"{impl_rel}: missing !benchmark code_aux slot def={name}",
                            location=impl_rel,
                        )
                    )

    # Spec files: no markers of any prefix
    for pkg in manifest.get("packages", []):
        for mod in pkg.get("modules", []):
            spec_rel = mod.get("spec")
            if not spec_rel:
                continue
            spec_path = _abs(benchmark, spec_rel)
            if not spec_path.exists():
                continue
            markers = parse_file_markers(spec_path)
            if markers:
                details.append(
                    Finding(
                        "error",
                        f"{spec_rel}: Spec files must be marker-free "
                        f"(found {len(markers)} markers, first at line {markers[0].line_no})",
                        location=spec_rel,
                    )
                )

    # Non-editable: Harness, Test, root hub, lakefile
    files = manifest.get("files", {})
    for role in ("harness", "test", "root_hub"):
        rel = files.get(role)
        if not rel:
            continue
        path = _abs(benchmark, rel)
        if not path.exists() or path.suffix != ".lean":
            continue
        markers = parse_file_markers(path)
        if markers:
            details.append(
                Finding(
                    "error",
                    f"{rel} ({role}) is non-editable and must be marker-free "
                    f"(found {len(markers)} markers)",
                    location=rel,
                )
            )

    status = "fail" if any(f.severity == "error" for f in details) else "pass"
    return CheckResult("file_roles", status, details)


# ─────────────────────────────────────────────────────────────
# Check: spec shape (RepoImpl → Prop; no theorems in Spec files)


_DEF_SPEC_HEADER_RE = re.compile(
    rf"^\s*{_DEF_MOD}def\s+(spec_[\w?!']+)\s*(?P<body>[\s\S]*?)\s*:=",
    re.MULTILINE,
)
_SPEC_PROP_RE = re.compile(
    r"\(\s*_?\w+\s*:\s*RepoImpl\s*\)\s*:\s*Prop\b",
)
_THEOREM_IN_SPEC_RE = re.compile(r"^\s*(theorem|lemma|example)\b")
_OPAQUE_SPEC_HELPER_RE = re.compile(r"^\s*(opaque|axiom)\b.*\bRepoImpl\b.*\bProp\b")
_DEF_SPEC_FULL_RE = re.compile(
    rf"^\s*{_DEF_MOD}def\s+(spec_[\w?!']+)\s*(?P<header>[\s\S]*?)\s*:=\s*(?P<body>[\s\S]*?)(?=^\s*(?:{_DEF_MOD}def|theorem|lemma|example|/--|/-!|namespace\b|end\b)|\Z)",
    re.MULTILINE,
)


def check_spec_shape(benchmark: Path) -> CheckResult:
    """Every manifest-listed spec is typed `(impl : RepoImpl) : Prop`; no theorems in Spec files.

    Spec obligations should be manifest-addressable. A ``def spec_*`` in
    ``Spec/`` that is neither listed under ``specs`` nor explicitly
    acknowledged under ``spec_helpers`` is curation drift: generation/eval will
    silently ignore it.
    """
    manifest, errors = _load_manifest(benchmark)
    if manifest is None:
        return CheckResult("spec_shape", "fail", errors)

    details: list[Finding] = []

    for pkg in manifest.get("packages", []):
        for mod in pkg.get("modules", []):
            spec_rel = mod.get("spec")
            if not spec_rel:
                continue
            spec_path = _abs(benchmark, spec_rel)
            if not spec_path.exists():
                continue
            text = spec_path.read_text()
            # Strip block comments so docstring text mentioning "theorem"
            # does not false-trigger the theorem-in-spec check.
            text_no_comments = _strip_block_comments(text)

            for i, line in enumerate(text_no_comments.splitlines(), start=1):
                if _THEOREM_IN_SPEC_RE.match(line):
                    details.append(
                        Finding(
                            "error",
                            f"{spec_rel}:{i}: theorem/lemma/example not allowed in Spec file "
                            "(proofs live in Proof/ or are agent-generated)",
                            location=f"{spec_rel}:{i}",
                        )
                    )

            listed_specs = _manifest_name_set(mod.get("specs", []))
            helper_specs = _manifest_name_set(mod.get("spec_helpers", []))
            spec_defs_in_file: set[str] = set()
            for m in _DEF_SPEC_HEADER_RE.finditer(text):
                spec_name = m.group(1)
                spec_defs_in_file.add(spec_name)
                header = m.group("body")
                if spec_name in listed_specs and not _SPEC_PROP_RE.search(header):
                    details.append(
                        Finding(
                            "error",
                            f"{spec_rel}: spec {spec_name!r} is not typed "
                            "`(impl : RepoImpl) : Prop`",
                            location=spec_rel,
                        )
                    )
            unmanifested = sorted(spec_defs_in_file - listed_specs - helper_specs)
            if unmanifested:
                details.append(
                    Finding(
                        "error",
                        f"{spec_rel}: {len(unmanifested)} `def spec_*` declaration(s) "
                        "are not listed in manifest specs/spec_helpers: "
                        f"{unmanifested[:10]}"
                        + (" ..." if len(unmanifested) > 10 else ""),
                        location=spec_rel,
                    )
                )

    status = "fail" if any(f.severity == "error" for f in details) else "pass"
    return CheckResult("spec_shape", status, details)


# ─────────────────────────────────────────────────────────────
# Check: spec quality (cheap non-vacuity signals)


def _collect_spec_bodies(text: str) -> dict[str, tuple[str, str]]:
    """Return {spec_name: (header, body)} for top-level spec defs."""
    out: dict[str, tuple[str, str]] = {}
    for m in _DEF_SPEC_FULL_RE.finditer(text):
        out[m.group(1)] = (m.group("header"), m.group("body"))
    return out


def check_spec_quality(benchmark: Path) -> CheckResult:
    """Warn on manifest-listed specs that look vacuous or disconnected from RepoImpl."""
    manifest, errors = _load_manifest(benchmark)
    if manifest is None:
        return CheckResult("spec_quality", "fail", errors)

    details: list[Finding] = []

    for pkg in manifest.get("packages", []):
        for mod in pkg.get("modules", []):
            spec_rel = mod.get("spec")
            if not spec_rel:
                continue
            spec_path = _abs(benchmark, spec_rel)
            if not spec_path.exists():
                continue
            text = spec_path.read_text()
            bodies = _collect_spec_bodies(text)
            for spec_name in _manifest_name_set(mod.get("specs", [])):
                if spec_name not in bodies:
                    continue
                header, body = bodies[spec_name]
                clean_body = _strip_line_comments(_strip_block_comments(body)).strip()
                impl_match = re.search(r"\(\s*(_?\w+)\s*:\s*RepoImpl\s*\)", header)
                impl_name = impl_match.group(1) if impl_match else None
                if impl_name and not impl_name.startswith("_"):
                    if not re.search(
                        rf"(?<![\w?!']){re.escape(impl_name)}(?![\w?!'])",
                        clean_body,
                    ):
                        details.append(
                            Finding(
                                "warn",
                                f"spec {spec_name!r} does not reference its RepoImpl parameter; "
                                "it may be a theorem-only/library fact rather than an implementation obligation",
                                location=spec_rel,
                            )
                        )
                elif impl_name and impl_name.startswith("_"):
                    details.append(
                        Finding(
                            "warn",
                            f"spec {spec_name!r} intentionally ignores RepoImpl via parameter {impl_name!r}; "
                            "confirm this is not a vacuous benchmark obligation",
                            location=spec_rel,
                        )
                    )

                body_one_line = re.sub(r"\s+", " ", clean_body)
                if body_one_line == "True" or re.search(
                    r"(?:->|→|=>)\s*True\s*$",
                    body_one_line,
                ):
                    details.append(
                        Finding(
                            "warn",
                            f"spec {spec_name!r} has a body or final implication that is `True`; "
                            "this is likely vacuous unless it is an intentional placeholder",
                            location=spec_rel,
                        )
                    )

    return CheckResult("spec_quality", "warn" if details else "pass", details)


# ─────────────────────────────────────────────────────────────
# Check: translated manifest source alignment


_SOURCE_PROVENANCE_KEYS = (
    "source_id",
    "stable_source_id",
    "source_signature",
    "upstream_name",
    "source_theorem",
    "source_spec",
    "source_name",
    "source_file",
)
_SOURCE_PROVENANCE_LIST_KEYS = ("source_ids", "source_theorems", "source_specs")


def _has_manifest_source_provenance(item: object) -> bool:
    if not isinstance(item, dict):
        return False
    if any(
        isinstance(item.get(key), str) and item[key].strip()
        for key in _SOURCE_PROVENANCE_KEYS
    ):
        return True
    return any(
        isinstance(item.get(key), list)
        and any(isinstance(value, str) and value.strip() for value in item[key])
        for key in _SOURCE_PROVENANCE_LIST_KEYS
    )


def check_source_alignment(benchmark: Path) -> CheckResult:
    """Warn when translated manifest items do not carry source provenance."""
    manifest, errors = _load_manifest(benchmark)
    if manifest is None:
        return CheckResult("source_alignment", "fail", errors)

    source = manifest.get("source", {})
    if not (
        isinstance(source, dict)
        and (source.get("kind") == "translated" or source.get("language"))
    ):
        return CheckResult(
            "source_alignment",
            "pass",
            [
                Finding(
                    "info",
                    "benchmark is not marked translated; source alignment check inactive",
                )
            ],
        )

    missing: list[str] = []
    for pkg, mod in _iter_manifest_modules(manifest):
        for collection in ("types", "apis", "api_helpers", "specs", "spec_helpers"):
            for item in mod.get(collection, []):
                if _has_manifest_source_provenance(item):
                    continue
                name = item.get("name") if isinstance(item, dict) else item
                missing.append(
                    f"manifest.json:{pkg.get('name')}.{mod.get('name')}.{collection}.{name}"
                )

    if not missing:
        return CheckResult(
            "source_alignment",
            "pass",
            [Finding("info", "all translated manifest items carry source provenance")],
        )
    return CheckResult(
        "source_alignment",
        "warn",
        [
            Finding(
                "warn",
                f"{len(missing)} translated manifest item(s) lack source provenance. Examples: {missing[:10]}",
                location=missing[0],
            )
        ],
    )


# ─────────────────────────────────────────────────────────────
# Check: API/spec coverage


def check_api_spec_coverage(benchmark: Path) -> CheckResult:
    """Warn when manifest APIs are not mentioned by any manifest-listed spec."""
    manifest, errors = _load_manifest(benchmark)
    if manifest is None:
        return CheckResult("api_spec_coverage", "fail", errors)

    spec_text = ""
    for pkg in manifest.get("packages", []):
        for mod in pkg.get("modules", []):
            spec_rel = mod.get("spec")
            if not spec_rel:
                continue
            spec_path = _abs(benchmark, spec_rel)
            if spec_path.exists():
                clean = _strip_line_comments(
                    _strip_block_comments(spec_path.read_text())
                )
                spec_text += "\n" + clean

    missing: list[str] = []
    for pkg in manifest.get("packages", []):
        for mod in pkg.get("modules", []):
            for api in mod.get("apis", []):
                if api.get("kind", "api") != "api":
                    continue
                name = api.get("name")
                if not name:
                    continue
                tail = name.rsplit(".", 1)[-1]
                if not re.search(
                    rf"(?<![\w?!']){re.escape(tail)}(?![\w?!'])", spec_text
                ):
                    missing.append(name)

    details: list[Finding] = []
    if missing:
        details.append(
            Finding(
                "warn",
                f"{len(missing)} manifest API(s) are not mentioned by any Spec file: "
                f"{missing[:10]}" + (" ..." if len(missing) > 10 else ""),
            )
        )
    return CheckResult("api_spec_coverage", "warn" if details else "pass", details)


# ─────────────────────────────────────────────────────────────
# Check: translated-source provenance


def check_provenance(benchmark: Path) -> CheckResult:
    """Check translated benchmarks have source metadata plus a validator-readable map."""
    manifest, errors = _load_manifest(benchmark)
    if manifest is None:
        return CheckResult("provenance", "fail", errors)

    source = manifest.get("source", {})
    details: list[Finding] = []
    if not isinstance(source, dict):
        return CheckResult(
            "provenance",
            "warn",
            [Finding("warn", "manifest.source is not an object")],
        )

    is_translated = source.get("kind") == "translated" or bool(source.get("language"))
    if not is_translated:
        return CheckResult("provenance", "pass", [])

    missing_meta = [
        key
        for key in ("language", "repo_url", "commit_hash", "path")
        if not source.get(key)
    ]
    if missing_meta:
        details.append(
            Finding(
                "warn",
                f"translated benchmark source metadata missing: {missing_meta}",
                location="manifest.json",
            )
        )

    provenance_candidates = [
        benchmark / ".vero" / "discover.json",
        benchmark / ".vero" / "discovery_report.json",
        benchmark / ".vero" / "selection_plan.json",
        benchmark / ".vero" / "plan.json",
        benchmark / ".vero" / "source_map.json",
        benchmark / "curation" / "discovery_report.json",
    ]
    if not any(path.exists() for path in provenance_candidates):
        details.append(
            Finding(
                "warn",
                "translated benchmark has no validator-readable source provenance artifact "
                "(.vero/source_map.json, discover.json, selection_plan.json, or plan.json)",
            )
        )

    return CheckResult("provenance", "warn" if details else "pass", details)


# ─────────────────────────────────────────────────────────────
# Check: trusted boundary audit signal


_BENCHMARK_SPECIFIC_TRUST_TERMS = {
    "owner",
    "smashed",
    "self_call",
    "self_calls",
    "serialize",
    "deserialize",
    "parser",
    "validator",
}


def check_trusted_boundary(benchmark: Path) -> CheckResult:
    """Warn when trusted axioms/shims need human boundary review."""
    manifest, errors = _load_manifest(benchmark)
    if manifest is None:
        return CheckResult("trusted_boundary", "fail", errors)

    trusted = [str(name) for name in manifest.get("trusted_axioms", [])]
    if not trusted:
        return CheckResult("trusted_boundary", "pass", [])

    details: list[Finding] = [
        Finding(
            "info",
            f"{len(trusted)} trusted axiom(s)/opaque primitive(s) declared in manifest; "
            "confirm each is external framework/library semantics, not a benchmark-specific shortcut",
            location="manifest.json",
        )
    ]
    risky = [
        name
        for name in trusted
        if any(term in name.lower() for term in _BENCHMARK_SPECIFIC_TRUST_TERMS)
    ]
    if risky:
        details.append(
            Finding(
                "warn",
                "trusted names contain benchmark-specific terms and need explicit source-backed rationale: "
                f"{risky[:10]}" + (" ..." if len(risky) > 10 else ""),
                location="manifest.json",
            )
        )

    return CheckResult("trusted_boundary", "warn" if risky else "pass", details)


# ─────────────────────────────────────────────────────────────
# Check: source index artifact


SOURCE_INDEX_RULES = (
    "error: source_index.json must be a JSON object with version=1 and an entities/items list",
    "error: each entity must be an object with id, name, kind, source_file, and positive integer source_line",
    "error: entity ids must be unique",
    "error: source_file must be a relative path contained in the source tree",
    "error: role/default_role and disposition values must use the supported vocabularies",
    "error: dropped entities require drop_reason/reason; axiomatized entities require trusted_external or requires_human_review",
    "error: dependencies must be a list when present",
    "error: selected entities must not depend on missing, dropped, or unselected source_index ids",
    "warn: source_index.json is absent, empty, lacks source_path/source_language/generated_at, or points at inaccessible source files",
    "warn: dependencies that reference ids outside the index may indicate an incomplete inventory",
)


def _source_index_path(
    benchmark: Path,
) -> tuple[dict | None, Path | None, list[Finding]]:
    return _load_first_json(benchmark, ["source_index.json"])


def _source_index_entities(source_index: dict) -> list:
    entities = source_index.get("entities")
    if entities is None:
        entities = source_index.get("items")
    return entities if isinstance(entities, list) else []


def _is_relative_safe_path(value: str) -> bool:
    path = Path(value)
    return bool(value) and not path.is_absolute() and ".." not in path.parts


def check_source_index(benchmark: Path) -> CheckResult:
    """Validate the source-wide no-LLM inventory artifact.

    Rule layers:

    Error:
    - The artifact must be a JSON object with ``version=1`` and an
      ``entities``/``items`` list.
    - Each entity must carry stable identity/location fields:
      ``id``, ``name``, ``kind``, ``source_file``, and positive integer
      ``source_line``.
    - Entity ids must be unique, source files must be relative/safe, role and
      disposition metadata must use the supported vocabulary, and dependencies
      must be lists.

    Warning:
    - Missing or empty source indexes, missing producer metadata, inaccessible
      source files, and unknown dependency ids are quality signals rather than
      hard blockers because hand-written benchmarks and moved artifacts may not
      have a live source tree.
    """
    source_index, source_path, load_errors = _source_index_path(benchmark)
    if load_errors:
        return CheckResult("source_index", "fail", load_errors)
    if source_index is None:
        return CheckResult(
            "source_index",
            "warn",
            [
                Finding(
                    "info",
                    "no source_index.json found; source-index artifact checks skipped "
                    "(normal for hand-crafted benchmarks)",
                )
            ],
        )
    location = str(source_path) if source_path else "source_index.json"

    details: list[Finding] = []
    if not isinstance(source_index, dict):
        return CheckResult(
            "source_index",
            "fail",
            [Finding("error", "source_index.json must be a JSON object", location)],
        )

    if source_index.get("version") != 1:
        details.append(
            Finding(
                "error",
                f"source_index version must be 1, got {source_index.get('version')!r}",
                location,
            )
        )

    raw_entities = source_index.get("entities")
    if raw_entities is None:
        raw_entities = source_index.get("items")
    if not isinstance(raw_entities, list):
        details.append(
            Finding(
                "error",
                "source_index must contain an entities/items list",
                location,
            )
        )
        raw_entities = []
    if not raw_entities:
        details.append(Finding("warn", "source_index contains no entities", location))

    if not source_index.get("source_language"):
        details.append(
            Finding("warn", "source_index missing source_language", location)
        )
    if not source_index.get("generated_at"):
        details.append(Finding("warn", "source_index missing generated_at", location))

    source_root: Path | None = None
    source_path_value = source_index.get("source_path")
    if source_path_value:
        source_root = Path(str(source_path_value))
        if not source_root.exists():
            details.append(
                Finding(
                    "warn",
                    f"source_index source_path is not accessible: {source_root}",
                    location,
                )
            )
    else:
        details.append(Finding("warn", "source_index missing source_path", location))

    seen_ids: set[str] = set()
    duplicate_ids: set[str] = set()
    dependency_refs: list[tuple[str, str, str, bool]] = []
    entities_by_id: dict[str, dict] = {}
    for i, raw in enumerate(raw_entities):
        entity_loc = f"{location}:entities[{i}]"
        if not isinstance(raw, dict):
            details.append(
                Finding("error", "source_index entity must be an object", entity_loc)
            )
            continue

        entity_id = str(raw.get("id", "")).strip()
        if not entity_id:
            details.append(
                Finding("error", "source_index entity missing id", entity_loc)
            )
        elif entity_id in seen_ids:
            duplicate_ids.add(entity_id)
        else:
            seen_ids.add(entity_id)
            entities_by_id[entity_id] = raw

        for key in ("name", "kind", "source_file"):
            if not str(raw.get(key, "")).strip():
                details.append(
                    Finding("error", f"source_index entity missing {key}", entity_loc)
                )

        source_file = str(raw.get("source_file", "")).strip()
        if source_file:
            if not _is_relative_safe_path(source_file):
                details.append(
                    Finding(
                        "error",
                        f"source_file must be a relative path within the source tree: {source_file!r}",
                        entity_loc,
                    )
                )
            elif source_root is not None and source_root.exists():
                if not (source_root / source_file).exists():
                    details.append(
                        Finding(
                            "warn",
                            f"source_file is not accessible under source_path: {source_file}",
                            entity_loc,
                        )
                    )

        source_line = raw.get("source_line")
        if not isinstance(source_line, int) or source_line <= 0:
            details.append(
                Finding(
                    "error",
                    f"source_line must be a positive integer, got {source_line!r}",
                    entity_loc,
                )
            )

        details.extend(
            _validate_role_payload(
                raw,
                location=entity_loc,
                default_required=True,
            )
        )

        dependencies = raw.get("dependencies", [])
        if dependencies is None:
            dependencies = []
        if not isinstance(dependencies, list):
            details.append(Finding("error", "dependencies must be a list", entity_loc))
        else:
            for dep in dependencies:
                if isinstance(dep, str):
                    dependency_refs.append(
                        (
                            entity_id or f"entities[{i}]",
                            dep,
                            entity_loc,
                            raw.get("selected") is True,
                        )
                    )
                else:
                    details.append(
                        Finding(
                            "warn",
                            f"dependency reference is not a string id: {dep!r}",
                            entity_loc,
                        )
                    )

    for entity_id in sorted(duplicate_ids):
        details.append(
            Finding(
                "error",
                f"duplicate source_index entity id: {entity_id}",
                location,
            )
        )

    for owner, dep, entity_loc, owner_selected in dependency_refs:
        if dep not in seen_ids:
            details.append(
                Finding(
                    "error" if owner_selected else "warn",
                    f"{owner}: dependency id {dep!r} is not present in source_index",
                    entity_loc,
                )
            )
            continue
        dep_entity = entities_by_id.get(dep)
        if (
            owner_selected
            and dep_entity is not None
            and (
                dep_entity.get("selected") is False
                or (dep_entity.get("role") or dep_entity.get("default_role"))
                == "dropped_with_reason"
                or dep_entity.get("semantic_disposition") == "dropped"
            )
        ):
            details.append(
                Finding(
                    "error",
                    f"{owner}: dependency id {dep!r} is dropped or unselected in source_index",
                    entity_loc,
                )
            )

    if not details:
        details.append(
            Finding(
                "info",
                f"{len(raw_entities)} source-index entity/entities validated",
                location,
            )
        )

    status = (
        "fail"
        if any(f.severity == "error" for f in details)
        else ("warn" if any(f.severity == "warn" for f in details) else "pass")
    )
    return CheckResult("source_index", status, details)


# ─────────────────────────────────────────────────────────────
# Check: source coverage
#
# Diff `.vero/discover.json` (if present) against the manifest: every
# item the discover stage marked `selected: true` must either appear in
# the manifest's apis/specs or be explicitly marked `api_helper` /
# `spec_helper` / `general` via `kind=...`. Items from the source
# repo that are selected but unclassified surface as warnings.


def _load_selected_source_items(
    benchmark: Path,
) -> tuple[list[dict], str | None, list[Finding]]:
    """Load selected source entities from the newest known sidecar shape."""
    # Select is the first stage that turns the full source inventory into a
    # curated surface.  The no-LLM source_index stage may mark every entity as
    # selected=True to mean "present in the registry", so it is only a fallback.
    selection, selection_path, errors = _load_first_json(
        benchmark, ["select.json", "selection_plan.json"]
    )
    if errors:
        return [], str(selection_path) if selection_path else None, errors
    if selection is not None:
        raw = selection.get("selected_items") or []
        if not raw and selection.get("selected_entity_ids"):
            raw = [
                {"name": name, "selected": True}
                for name in selection["selected_entity_ids"]
            ]
        selected = [
            item
            for item in raw
            if item.get("selected", True)
            and item.get(
                "selection_stage_role",
                item.get("selection_role", item.get("role", item.get("default_role"))),
            )
            != "dropped_with_reason"
        ]
        return selected, str(selection_path), []

    # Current curation output shape produced by DiscoverStage.
    discovery, discovery_path, errors = _load_first_json(
        benchmark, ["discover.json", "discovery_report.json"]
    )
    if errors:
        return [], str(discovery_path) if discovery_path else None, errors
    if discovery is not None:
        raw = discovery.get("items") or discovery.get("entities") or []
        selected = [item for item in raw if item.get("selected", False)]
        return selected, str(discovery_path), []

    # Source index is a registry fallback only. If a selection plan exists, even
    # an empty one, it is authoritative over registry inventory.
    source_index, source_path, errors = _load_first_json(
        benchmark, ["source_index.json"]
    )
    if errors:
        return [], str(source_path) if source_path else None, errors
    if source_index is not None:
        raw = source_index.get("entities") or source_index.get("items") or []
        selected = [
            item
            for item in raw
            if item.get("selected", True)
            and item.get("role", item.get("default_role")) != "dropped_with_reason"
        ]
        return selected, str(source_path), []

    return [], None, []


def check_source_coverage(benchmark: Path) -> CheckResult:
    """Compare selected source entities to manifest entries.

    Supports both the intended `.vero/source_index.json` registry and
    current curation outputs (`curation/discovery_report.json`,
    `curation/selection_plan.json`). This fixes the previous false-skip where
    validation only looked for `.vero/discover.json`.
    """
    manifest, errors = _load_manifest(benchmark)
    if manifest is None:
        return CheckResult("source_coverage", "fail", errors)

    selected, source_path, load_errors = _load_selected_source_items(benchmark)
    if load_errors:
        return CheckResult("source_coverage", "fail", load_errors)

    if source_path is None:
        return CheckResult(
            "source_coverage",
            "warn",
            [
                Finding(
                    "info",
                    "no source registry/discover.json/discovery_report.json/selection_plan.json "
                    "— source coverage check skipped (normal for hand-crafted benchmarks)",
                )
            ],
        )

    plan, _plan_path, plan_errors = _load_plan(benchmark)
    if plan_errors:
        return CheckResult("source_coverage", "fail", plan_errors)

    api_names: set[str] = set()
    spec_names: set[str] = set()
    for pkg in manifest.get("packages", []):
        for mod in pkg.get("modules", []):
            for api in mod.get("apis", []):
                if name := api.get("name"):
                    api_names.add(name)
            for helper in mod.get("api_helpers", []):
                if name := helper.get("name"):
                    api_names.add(name)
            for spec in mod.get("specs", []):
                if isinstance(spec, dict):
                    if name := spec.get("name"):
                        spec_names.add(name)
                else:
                    spec_names.add(spec)
            for helper in mod.get("spec_helpers", []):
                if isinstance(helper, dict):
                    if name := helper.get("name"):
                        spec_names.add(name)
                else:
                    spec_names.add(helper)
    represented_source_ids = _collect_source_ref_ids(manifest)
    represented_names = _collect_decl_names(manifest)
    if plan is not None:
        represented_source_ids.update(_collect_source_ref_ids(plan))
        represented_names.update(_collect_decl_names(plan))

    details: list[Finding] = []
    missing: list[str] = []
    for item in selected:
        role = (
            item.get("role")
            or item.get("selection_stage_role")
            or item.get("selection_role")
            or item.get("default_role")
            or ""
        )
        if role == "dropped_with_reason":
            continue
        lean_name = (
            item.get("lean_name")
            or item.get("target_name")
            or item.get("name")
            or item.get("upstream_name")
            or item.get("qualified_name")
            or ""
        )
        if not lean_name:
            continue
        tail = lean_name.rsplit(".", 1)[-1]
        source_id = (
            item.get("stable_source_id")
            or item.get("source_id")
            or item.get("source_index_id")
            or item.get("id")
        )
        if isinstance(source_id, str) and source_id in represented_source_ids:
            continue
        if lean_name in represented_names or tail in represented_names:
            continue
        if tail in api_names or tail in spec_names:
            continue
        if tail.startswith("spec_") and tail in spec_names:
            continue
        # Items with category 'type', 'axiom', 'opaque' or explicit 'general' kind
        # are context and not required in apis/specs. We still warn if selected
        # but absent from any side.
        category = (
            item.get("category") or item.get("source_kind") or item.get("kind", "")
        )
        if category in {"type", "axiom", "opaque"} or role in {
            "trusted_external",
            "trusted_theory",
            "semantic_model",
            "spec_helper",
            "api_helper",
            "proof_helper_task",
            "trusted_theorem",
            "reference_api",
        }:
            continue
        missing.append(f"{category}:{lean_name}")

    if missing:
        details.append(
            Finding(
                "warn",
                f"{len(missing)} selected source item(s) not represented in "
                f"manifest apis/specs ({source_path}): {missing[:10]}"
                + (" …" if len(missing) > 10 else ""),
            )
        )
    else:
        details.append(
            Finding(
                "info",
                f"{len(selected)} selected item(s) round-tripped from {source_path}",
            )
        )

    status = "warn" if any(f.severity == "warn" for f in details) else "pass"
    return CheckResult("source_coverage", status, details)


# ─────────────────────────────────────────────────────────────
# Check: entity roles / dispositions


def _validate_role_payload(
    item: dict,
    *,
    location: str,
    default_required: bool = False,
) -> list[Finding]:
    details: list[Finding] = []
    role = item.get("role") or item.get("default_role")
    disposition = item.get("disposition")
    name = (
        item.get("name")
        or item.get("lean_name")
        or item.get("upstream_name")
        or "<unnamed>"
    )

    if default_required and not role:
        details.append(
            Finding(
                "error",
                f"{name}: missing role/default_role; every source-index entity must be classified",
                location=location,
            )
        )
    if role and role not in _ALLOWED_ENTITY_ROLES:
        details.append(
            Finding(
                "error",
                f"{name}: unknown role {role!r}; expected one of {sorted(_ALLOWED_ENTITY_ROLES)}",
                location=location,
            )
        )
    if disposition and disposition not in _ALLOWED_DISPOSITIONS:
        details.append(
            Finding(
                "error",
                f"{name}: unknown disposition {disposition!r}; expected one of {sorted(_ALLOWED_DISPOSITIONS)}",
                location=location,
            )
        )
    if role == "dropped_with_reason" and not (
        item.get("drop_reason") or item.get("reason")
    ):
        details.append(
            Finding(
                "error",
                f"{name}: role=dropped_with_reason requires drop_reason/reason",
                location=location,
            )
        )
    if disposition == "axiomatized" and role not in {
        "trusted_external",
        "requires_human_review",
    }:
        details.append(
            Finding(
                "error",
                f"{name}: disposition=axiomatized is only allowed for trusted_external or requires_human_review",
                location=location,
            )
        )
    return details


def check_entity_roles(benchmark: Path) -> CheckResult:
    """Validate optional role/disposition metadata in source registry + manifest."""
    manifest, errors = _load_manifest(benchmark)
    if manifest is None:
        return CheckResult("entity_roles", "fail", errors)

    details: list[Finding] = []

    source_index, source_path, load_errors = _load_first_json(
        benchmark, ["source_index.json"]
    )
    if load_errors:
        return CheckResult("entity_roles", "fail", load_errors)
    if source_index is not None:
        entities = source_index.get("entities") or source_index.get("items") or []
        for i, item in enumerate(entities):
            details.extend(
                _validate_role_payload(
                    item,
                    location=f"{source_path}:entities[{i}]",
                    default_required=True,
                )
            )
    else:
        details.append(
            Finding(
                "info",
                "no source_index.json found; role completeness is checked only for manifest entries",
            )
        )

    for _pkg, mod, api in _manifest_api_entries(manifest):
        loc = mod.get("impl", "manifest.json")
        details.extend(_validate_role_payload(api, location=loc))
    for _pkg, mod, spec in _manifest_spec_entries(manifest):
        loc = mod.get("spec", "manifest.json")
        details.extend(_validate_role_payload(spec, location=loc))

    status = (
        "fail"
        if any(f.severity == "error" for f in details)
        else ("warn" if any(f.severity == "warn" for f in details) else "pass")
    )
    return CheckResult("entity_roles", status, details)


# ─────────────────────────────────────────────────────────────
# Check: API/reference consistency


def _collect_manifest_apis(manifest: dict) -> list[tuple[str, str, dict, str]]:
    """Return (repo_impl_field, api_tail, api_entry, location) for apis[] items.

    This intentionally does not collect manifest ``specs``/``spec_helpers``.
    It also does not collect the dedicated ``api_helpers`` list: those names
    are vocabulary/helper declarations, not necessarily RepoImpl fields.
    """
    out: list[tuple[str, str, dict, str]] = []
    for pkg, mod, api in _manifest_api_entries(manifest):
        name = api.get("name")
        if not name:
            continue
        kind = api.get("kind", "api")
        if kind != "api":
            continue
        out.append(
            (
                pkg.get("repo_impl_field", ""),
                _normalize_name(name),
                api,
                mod.get("spec") or mod.get("impl") or "manifest.json",
            )
        )
    return out


def _lean_text_without_comments(text: str) -> str:
    return _strip_line_comments(_strip_block_comments(text))


def check_reference_consistency(benchmark: Path) -> CheckResult:
    """Specs must refer to manifest API items through RepoImpl.

    Build the API-name set from manifest ``apis[]`` entries, excluding specs
    and spec helpers. If a Spec file mentions one of those API symbols as a
    bare or namespace-qualified reference, the matched reference must begin
    with ``impl.``. Otherwise the spec is constraining a frozen translation
    item rather than an arbitrary ``impl : RepoImpl``.
    """
    manifest, errors = _load_manifest(benchmark)
    if manifest is None:
        return CheckResult("reference_consistency", "fail", errors)

    apis = _collect_manifest_apis(manifest)
    if not apis:
        return CheckResult(
            "reference_consistency",
            "pass",
            [Finding("info", "no manifest APIs found")],
        )

    details: list[Finding] = []
    for pkg, mod in _iter_manifest_modules(manifest):
        spec_rel = mod.get("spec")
        if not spec_rel:
            continue
        spec_path = _abs(benchmark, spec_rel)
        if not spec_path.exists():
            continue
        text = _lean_text_without_comments(spec_path.read_text(encoding="utf-8"))
        repo_field = pkg.get("repo_impl_field", "")
        for api_field, api_tail, _api, _loc in apis:
            if api_field != repo_field:
                continue
            # Catch bare or namespace-qualified references such as `encode` or
            # `Flocq.bpow`; ignore references rooted at `impl.`.
            pattern = re.compile(
                rf"(?<![\w])(?P<ref>(?:[A-Za-z_]\w*\.)*{re.escape(api_tail)})(?![\w'])"
            )
            for match in pattern.finditer(text):
                ref = match.group("ref")
                if ref.startswith("impl."):
                    continue
                # Avoid reporting the spec's own name if it happens to contain
                # the API tail as a suffix; the regex above requires a whole
                # identifier so this is mostly defensive.
                details.append(
                    Finding(
                        "error",
                        f"spec references manifest API {api_tail!r} as {ref!r}; "
                        "API references in Spec files must begin with `impl.`",
                        location=spec_rel,
                    )
                )
                break

    status = "fail" if any(f.severity == "error" for f in details) else "pass"
    if not details:
        details.append(
            Finding("info", "all scored API references in Spec files use RepoImpl")
        )
    return CheckResult("reference_consistency", status, details)


# ─────────────────────────────────────────────────────────────
# Check: trusted surface (`axiom` / `sorry`)


_AXIOM_DECL_RE = re.compile(r"^\s*axiom\s+([A-Za-z_][\w'.]*)\b", re.MULTILINE)
_SORRY_TOKEN_RE = re.compile(r"(?<![\w'])sorry(?![\w'])|(?<![\w'])admit(?![\w'])")


def _slot_text(lines: list[str], start_line: int, end_line: int) -> str:
    # Marker lines are 1-based. The editable content is strictly between them.
    return "\n".join(lines[start_line : end_line - 1])


def check_trusted_surface(benchmark: Path) -> CheckResult:
    """Reject unreviewed axioms and trusted-context sorry/admit leakage."""
    manifest, errors = _load_manifest(benchmark)
    if manifest is None:
        return CheckResult("trusted_surface", "fail", errors)

    trusted_axioms = set(manifest.get("trusted_axioms", []))
    trusted_tails = {_normalize_name(a) for a in trusted_axioms}
    axiom_sources = manifest.get("trusted_axiom_sources", {})
    sorry_severity = "warn" if _is_python_scaffold(manifest) else "error"
    details: list[Finding] = []

    files_to_scan: set[Path] = set()
    files = manifest.get("files", {})
    for role in ("root_hub", "harness", "test"):
        if rel := files.get(role):
            path = _abs(benchmark, rel)
            if path.exists() and path.suffix == ".lean":
                files_to_scan.add(path)
    for _pkg, mod in _iter_manifest_modules(manifest):
        for key in ("impl", "spec"):
            if rel := mod.get(key):
                path = _abs(benchmark, rel)
                if path.exists():
                    files_to_scan.add(path)

    for path in sorted(files_to_scan):
        rel = str(path.relative_to(benchmark))
        raw = path.read_text(encoding="utf-8")
        text = _lean_text_without_comments(raw)
        for m in _AXIOM_DECL_RE.finditer(text):
            name = m.group(1)
            if (
                name not in trusted_axioms
                and _normalize_name(name) not in trusted_tails
            ):
                details.append(
                    Finding(
                        "error",
                        f"untrusted axiom {name!r}; add it to trusted_axioms only for real external boundaries",
                        location=rel,
                    )
                )
            elif (
                name not in axiom_sources and _normalize_name(name) not in axiom_sources
            ):
                details.append(
                    Finding(
                        "warn",
                        f"trusted axiom {name!r} lacks trusted_axiom_sources metadata",
                        location=rel,
                    )
                )

        # Comments may mention "sorry"; code may not. Strip comments first.
        if _SORRY_TOKEN_RE.search(text):
            details.append(
                Finding(
                    sorry_severity,
                    "sorry/admit token appears in frozen trusted code",
                    location=rel,
                )
            )

        markers = parse_file_markers(path)
        pairs, _ = pair_slots(markers)
        lines = raw.splitlines()
        for slot in pairs:
            if slot.prefix != "benchmark":
                continue
            body = _lean_text_without_comments(
                _slot_text(lines, slot.start_line, slot.end_line)
            )
            if slot.key == "code" and _SORRY_TOKEN_RE.search(body):
                details.append(
                    Finding(
                        sorry_severity,
                        f"!benchmark code slot def={slot.def_name} contains sorry/admit; reference implementation must be real code",
                        location=f"{rel}:{slot.start_line}",
                    )
                )
            if _AXIOM_DECL_RE.search(body):
                details.append(
                    Finding(
                        "error",
                        f"!benchmark slot def={slot.def_name} declares an axiom",
                        location=f"{rel}:{slot.start_line}",
                    )
                )

    status = (
        "fail"
        if any(f.severity == "error" for f in details)
        else ("warn" if any(f.severity == "warn" for f in details) else "pass")
    )
    if not details:
        details.append(
            Finding("info", "no untrusted axioms or trusted-context sorry/admit tokens")
        )
    return CheckResult("trusted_surface", status, details)


# ─────────────────────────────────────────────────────────────
# Check: import delta / semantic split


_IMPORT_MODULE_RE = re.compile(
    r"^\s*import\s+([A-Za-z_][\w'.]*(?:\.[A-Za-z_][\w'.]*)*)", re.MULTILINE
)


def _path_to_module(path: str) -> str:
    if path.endswith(".lean"):
        path = path[:-5]
    return path.replace("/", ".")


def _generated_imports(benchmark: Path) -> list[tuple[str, str]]:
    imports: list[tuple[str, str]] = []
    for path in sorted(benchmark.rglob("*.lean")):
        if any(part.startswith(".") for part in path.relative_to(benchmark).parts):
            continue
        rel = str(path.relative_to(benchmark))
        text = path.read_text(encoding="utf-8")
        for imported in _IMPORT_MODULE_RE.findall(text):
            imports.append((rel, imported))
    return imports


def _load_plan(benchmark: Path) -> tuple[dict | None, Path | None, list[Finding]]:
    return _load_first_json(benchmark, ["plan.json"])


def check_import_delta(benchmark: Path) -> CheckResult:
    """Check that selected/planned modules are not silently dropped from imports."""
    manifest, errors = _load_manifest(benchmark)
    if manifest is None:
        return CheckResult("import_delta", "fail", errors)

    details: list[Finding] = []
    files = manifest.get("files", {})
    root_rel = files.get("root_hub")
    if not root_rel:
        return CheckResult(
            "import_delta",
            "fail",
            [Finding("error", "manifest files.root_hub not set")],
        )
    root_path = _abs(benchmark, root_rel)
    if not root_path.exists():
        return CheckResult(
            "import_delta",
            "fail",
            [Finding("error", f"root hub missing: {root_rel}", location=root_rel)],
        )
    root_imports = set(_IMPORT_MODULE_RE.findall(root_path.read_text(encoding="utf-8")))
    missing_import_severity = "warn" if _is_python_scaffold(manifest) else "error"

    expected_paths: set[str] = set()
    for _pkg, mod in _iter_manifest_modules(manifest):
        for key in ("impl", "spec"):
            if rel := mod.get(key):
                expected_paths.add(rel)
    for rel in (files.get("harness"), files.get("test")):
        if rel:
            expected_paths.add(rel)
    for pkg in manifest.get("packages", []):
        if rel := pkg.get("bundle"):
            expected_paths.add(rel)

    for rel in sorted(expected_paths):
        module = _path_to_module(rel)
        if module not in root_imports:
            details.append(
                Finding(
                    missing_import_severity,
                    f"root hub does not import manifest module {module}",
                    location=root_rel,
                )
            )

    expected_modules = {
        _path_to_module(root_rel),
        *(_path_to_module(rel) for rel in expected_paths),
    }
    expected_suffixes = {
        module.split(".", 1)[1] for module in expected_modules if "." in module
    }
    package_roots = {
        str(pkg.get("name")).strip()
        for pkg in manifest.get("packages", [])
        if str(pkg.get("name", "")).strip()
    }
    for rel, imported in _generated_imports(benchmark):
        root = imported.split(".", 1)[0]
        if root in package_roots or imported in expected_modules:
            continue
        import_suffix = imported.split(".", 1)[1] if "." in imported else imported
        if (
            any(imported.endswith(f".{module}") for module in expected_modules)
            or import_suffix in expected_suffixes
        ):
            details.append(
                Finding(
                    "error",
                    f"generated module import {imported} uses a non-canonical root for a manifest module",
                    location=rel,
                )
            )

    plan, plan_path, plan_errors = _load_plan(benchmark)
    if plan_errors:
        return CheckResult("import_delta", "fail", plan_errors)
    if plan is not None:
        planned_modules = {
            (pkg.get("name"), mod.get("name"))
            for pkg in plan.get("packages", [])
            for mod in pkg.get("modules", [])
        }
        manifest_modules = {
            (pkg.get("name"), mod.get("name"))
            for pkg, mod in _iter_manifest_modules(manifest)
        }
        missing = sorted(planned_modules - manifest_modules)
        for pkg_name, mod_name in missing:
            details.append(
                Finding(
                    "error",
                    f"planned module {pkg_name}.{mod_name} from {plan_path} is missing from manifest; this is a semantic split/drop",
                    location="manifest.json",
                )
            )
        planned_by_module = {
            (pkg.get("name"), mod.get("name")): mod
            for pkg in plan.get("packages", [])
            for mod in pkg.get("modules", [])
        }
        for pkg, mod in _iter_manifest_modules(manifest):
            planned = planned_by_module.get((pkg.get("name"), mod.get("name")))
            if not planned:
                continue
            planned_apis = {
                item.get("lean_name") or item.get("name")
                for collection in ("apis", "api_helpers")
                for item in planned.get(collection, [])
                if isinstance(item, dict)
            }
            for api in mod.get("apis", []):
                name = api.get("name") if isinstance(api, dict) else None
                if name and name not in planned_apis:
                    details.append(
                        Finding(
                            "error",
                            f"manifest API {pkg.get('name')}.{mod.get('name')}.{name} is not present in plan.json; this may include an unreviewed/proof-bearing API",
                            location="manifest.json",
                        )
                    )
            planned_specs = {
                item.get("name")
                for item in planned.get("specs", [])
                if isinstance(item, dict) and item.get("name")
            }
            for spec in mod.get("specs", []):
                name = _manifest_spec_name(spec)
                if name and name not in planned_specs:
                    details.append(
                        Finding(
                            "error",
                            f"manifest spec {pkg.get('name')}.{mod.get('name')}.{name} is not present in plan.json",
                            location="manifest.json",
                        )
                    )

    source_index, source_path, source_errors = _load_first_json(
        benchmark, ["source_index.json"]
    )
    if source_errors:
        return CheckResult("import_delta", "fail", source_errors)
    if source_index is not None:
        represented_sources: set[str] = set()
        if plan is not None:
            for pkg in plan.get("packages", []):
                for mod in pkg.get("modules", []):
                    for src in mod.get("upstream_files", []):
                        represented_sources.update(_source_path_variants(src))
        for _pkg, mod in _iter_manifest_modules(manifest):
            for src in mod.get("upstream_files", []):
                represented_sources.update(_source_path_variants(src))

        entities = source_index.get("entities") or source_index.get("items") or []
        for item in entities:
            role = item.get("role") or item.get("default_role")
            if role == "dropped_with_reason":
                continue
            src = item.get("source_file") or item.get("file")
            if not src:
                continue
            if represented_sources and not (
                _source_path_variants(src) & represented_sources
            ):
                details.append(
                    Finding(
                        "warn",
                        f"source entity {item.get('name') or item.get('upstream_name')} from {src} is not represented in plan/manifest upstream_files",
                        location=str(source_path),
                    )
                )

    status = (
        "fail"
        if any(f.severity == "error" for f in details)
        else ("warn" if any(f.severity == "warn" for f in details) else "pass")
    )
    if not details:
        details.append(
            Finding(
                "info",
                "root imports cover manifest modules; no planned modules dropped",
            )
        )
    return CheckResult("import_delta", status, details)


# ─────────────────────────────────────────────────────────────
# Check: semantic weakening metadata


def _semantic_items_from_plan_or_manifest(
    manifest: dict,
    plan: dict | None,
) -> list[tuple[dict, str]]:
    items: list[tuple[dict, str]] = []
    if plan is not None:
        for mapping in plan.get("semantic_mappings", []):
            items.append((mapping, "plan.json"))
        for pkg in plan.get("packages", []):
            for mod in pkg.get("modules", []):
                for spec in mod.get("specs", []):
                    items.append((spec, f"plan:{pkg.get('name')}.{mod.get('name')}"))
        if items:
            return items

    for _pkg, mod, spec in _manifest_spec_entries(manifest):
        items.append((spec, mod.get("spec", "manifest.json")))
    for mapping in manifest.get("semantic_mappings", []):
        items.append((mapping, "manifest.json"))
    return items


_PLACEHOLDER_DEF_RE = re.compile(
    r"(?s)\b(?:noncomputable\s+)?def\s+[\w?!'.]+.*?:=\s*(?:default|false|none|\[\])\s*(?:$|--|\n)"
)
_UNIT_HELPER_RE = re.compile(
    r"(?s)\b(?:noncomputable\s+)?def\s+[\w?!'.]+.*?:\s*Unit\s*:=\s*\(\s*\)\s*(?:$|--|\n)"
)
_UNIT_ABBREV_RE = re.compile(r"(?m)^\s*abbrev\s+\w+\s*:=\s*Unit\s*(?:$|--)")
_UNIT_FIELD_RE = re.compile(r"(?m)^\s+\w+\s*:\s*Unit\s*(?:$|--)")


def _plan_placeholder_semantics(plan: dict | None) -> list[Finding]:
    """Flag plan helpers/types that freeze unknown semantics as placeholders."""
    if plan is None:
        return []

    details: list[Finding] = []
    collections = ("types", "api_helpers", "spec_helpers")
    for pkg in plan.get("packages", []):
        pkg_name = pkg.get("name")
        for mod in pkg.get("modules", []):
            location = f"plan:{pkg_name}.{mod.get('name')}"
            for collection in collections:
                for item in mod.get(collection, []):
                    if not isinstance(item, dict):
                        continue
                    if item.get("allow_placeholder_semantics"):
                        continue
                    lean_form = item.get("lean_form")
                    if not isinstance(lean_form, str):
                        continue
                    name = item.get("lean_name") or item.get("name") or "<unnamed>"
                    if _PLACEHOLDER_DEF_RE.search(lean_form):
                        details.append(
                            Finding(
                                "error",
                                f"{collection} {name} uses a noncomputable placeholder body (`default`, `false`, `none`, or `[]`)",
                                location=location,
                            )
                        )
                    if _UNIT_HELPER_RE.search(lean_form):
                        details.append(
                            Finding(
                                "error",
                                f"{collection} {name} freezes helper semantics as `Unit := ()`",
                                location=location,
                            )
                        )
                    if collection == "types" and (
                        _UNIT_ABBREV_RE.search(lean_form)
                        or _UNIT_FIELD_RE.search(lean_form)
                    ):
                        details.append(
                            Finding(
                                "error",
                                f"type {name} erases model state to `Unit`",
                                location=location,
                            )
                        )
    return details


_POLICY_ARTIFACT_FIELDS = (
    (
        "trusted_boundary_policy",
        "trusted_boundary_policy_artifact",
        "trusted_boundary_policy_status",
    ),
    (
        "representation_policy",
        "representation_policy_artifact",
        "representation_policy_status",
    ),
    (
        "macro_expansion_requirement",
        "macro_expansion_requirement_artifact",
        "macro_expansion_requirement_status",
    ),
)


def _iter_plan_items(plan: dict) -> Any:
    for pkg in plan.get("packages", []):
        pkg_name = pkg.get("name")
        for mod in pkg.get("modules", []):
            mod_name = mod.get("name")
            for collection in ("apis", "api_helpers", "specs", "spec_helpers"):
                for item in mod.get(collection, []):
                    if isinstance(item, dict):
                        yield pkg_name, mod_name, collection, item


def _resolve_plan_artifact(
    benchmark: Path,
    plan_path: Path | None,
    artifact: str,
) -> Path | None:
    artifact_path = Path(artifact)
    if artifact_path.is_absolute() or ".." in artifact_path.parts:
        return None

    bases = [benchmark]
    if plan_path is not None:
        bases.append(plan_path.parent)
        if plan_path.parent.name == ".vero":
            bases.append(plan_path.parent.parent)
    bases.extend(_workspace_candidates(benchmark))

    for base in dict.fromkeys(bases):
        candidate = base / artifact_path
        if candidate.exists():
            return candidate
    return None


def _status_indicates_blocked(value: object) -> bool:
    if not isinstance(value, str):
        return False
    lowered = value.lower()
    return any(
        marker in lowered
        for marker in (
            "blocked",
            "pending",
            "requires",
            "required",
            "not_waived",
            "unclear",
            "incomplete",
        )
    )


def _item_retains_policy_blocker(item: dict) -> bool:
    if _status_indicates_blocked(item.get("promotion_status")):
        return True
    if _status_indicates_blocked(item.get("review_status")):
        return True
    if _status_indicates_blocked(item.get("equivalence_status")):
        return True
    if item.get("requires_human_review") or item.get("degrade_to_structural_surrogate"):
        return True
    bridge = item.get("semantic_bridge_required") or item.get("bridge_lemmas_required")
    return bool(bridge)


def _promotion_effect_forbids_clearance(effect: object) -> bool:
    if not isinstance(effect, dict):
        return False
    for key, value in effect.items():
        if not isinstance(key, str):
            continue
        if key.startswith(("may_clear", "may_waive")) and value is False:
            return True
        if key.startswith("requires_") and value is True:
            return True
    return False


def _artifact_allows_clearance(status: object, effect: object) -> bool:
    return not _status_indicates_blocked(status) and not (
        _promotion_effect_forbids_clearance(effect)
    )


def _load_source_index_entities_by_id(
    benchmark: Path,
) -> tuple[dict[str, dict] | None, list[Finding]]:
    source_index, _source_path, source_errors = _load_first_json(
        benchmark, ["source_index.json"]
    )
    if source_errors:
        return None, source_errors
    if source_index is None:
        return None, []
    return (
        {
            str(entity.get("id")): entity
            for entity in _source_index_entities(source_index)
            if isinstance(entity, dict) and entity.get("id")
        },
        [],
    )


def _validate_macro_expansion_clearance_evidence(
    benchmark: Path,
    artifact_data: dict,
    artifact_path: Path,
) -> list[Finding]:
    """Approved macro artifacts need type-specific source-index evidence."""
    details: list[Finding] = []
    evidence = artifact_data.get("source_index_evidence")
    if not isinstance(evidence, list) or not evidence:
        return [
            Finding(
                "error",
                "approved macro expansion requirement needs non-empty source_index_evidence list",
                location=str(artifact_path),
            )
        ]

    entities, source_errors = _load_source_index_entities_by_id(benchmark)
    if source_errors:
        return source_errors
    if entities is None:
        return [
            Finding(
                "error",
                "approved macro expansion requirement needs source_index.json for source_index_evidence",
                location=str(artifact_path),
            )
        ]

    for idx, entry in enumerate(evidence):
        entry_loc = f"{artifact_path}:source_index_evidence[{idx}]"
        if not isinstance(entry, dict):
            details.append(
                Finding(
                    "error",
                    "source_index_evidence entries must be objects",
                    location=entry_loc,
                )
            )
            continue
        source_id = entry.get("source_id")
        if not isinstance(source_id, str) or not source_id:
            details.append(
                Finding(
                    "error",
                    "source_index_evidence entry missing source_id",
                    location=entry_loc,
                )
            )
            continue
        if _is_planner_source_ref(source_id):
            details.append(
                Finding(
                    "error",
                    "source_index_evidence source_id must be a source-index id, not planner:*",
                    location=entry_loc,
                )
            )
            continue
        for required in ("type_name", "generated_role"):
            if not isinstance(entry.get(required), str) or not entry.get(required):
                details.append(
                    Finding(
                        "error",
                        f"source_index_evidence entry missing {required}",
                        location=entry_loc,
                    )
                )
        entity = entities.get(source_id)
        if entity is None:
            details.append(
                Finding(
                    "error",
                    f"source_index_evidence references missing source_index id {source_id!r}",
                    location=entry_loc,
                )
            )
            continue
        if entity.get("selected") is False or (
            entity.get("semantic_disposition") == "dropped"
        ):
            details.append(
                Finding(
                    "error",
                    f"source_index_evidence references dropped/unselected source_index id {source_id!r}",
                    location=entry_loc,
                )
            )
        entity_kind = str(entity.get("kind") or entity.get("role") or "").lower()
        if entity_kind in {
            "macro_rules",
            "macro_template",
            "macro_generated_fn_template",
            "macro_generated_proof_template",
            "template",
        } or entity_kind.endswith("_template"):
            details.append(
                Finding(
                    "error",
                    f"source_index_evidence id {source_id!r} is a generic macro template, not type-specific generated evidence",
                    location=entry_loc,
                )
            )
        semantic_disposition = str(entity.get("semantic_disposition") or "").lower()
        if "incomplete" in semantic_disposition or "blocked" in semantic_disposition:
            details.append(
                Finding(
                    "error",
                    f"source_index_evidence id {source_id!r} is marked {semantic_disposition!r}, not approved generated evidence",
                    location=entry_loc,
                )
            )
    return details


def _iter_available_source_index_trace_records(
    artifact_data: dict,
    artifact_path: Path,
) -> tuple[list[tuple[str, str]], list[Finding]]:
    """Return source-index ids listed as non-clearing artifact trace evidence."""
    field = "available_source_index_trace_records"
    trace_records = artifact_data.get(field)
    if trace_records is None:
        return [], []

    refs: list[tuple[str, str]] = []
    details: list[Finding] = []
    if isinstance(trace_records, list):
        groups = [("<root>", trace_records)]
    elif isinstance(trace_records, dict):
        groups = list(trace_records.items())
    else:
        return [], [
            Finding(
                "error",
                f"{field} must be a list of source-index ids or an object mapping names to id lists",
                location=str(artifact_path),
            )
        ]

    for group_name, group_refs in groups:
        group_loc = f"{artifact_path}:{field}.{group_name}"
        if not isinstance(group_name, str) or not group_name:
            details.append(
                Finding(
                    "error",
                    f"{field} group names must be non-empty strings",
                    location=str(artifact_path),
                )
            )
            continue
        if not isinstance(group_refs, list):
            details.append(
                Finding("error", f"{field} group must be a list", location=group_loc)
            )
            continue
        for idx, source_id in enumerate(group_refs):
            ref_loc = f"{group_loc}[{idx}]"
            if not isinstance(source_id, str) or not source_id:
                details.append(
                    Finding(
                        "error",
                        f"{field} entries must be non-empty source-index id strings",
                        location=ref_loc,
                    )
                )
                continue
            refs.append((source_id, ref_loc))
    return refs, details


def _source_index_entity_is_template(entity: dict) -> bool:
    entity_kind = str(entity.get("kind") or entity.get("role") or "").lower()
    return entity_kind in {
        "macro_rules",
        "macro_template",
        "macro_generated_fn_template",
        "macro_generated_proof_template",
        "template",
    } or entity_kind.endswith("_template")


def _validate_available_source_index_trace_records(
    benchmark: Path,
    artifact_data: dict,
    artifact_path: Path,
) -> list[Finding]:
    """Non-clearing trace lists must still point at real selected source ids."""
    refs, details = _iter_available_source_index_trace_records(
        artifact_data, artifact_path
    )
    if not refs:
        return details

    entities, source_errors = _load_source_index_entities_by_id(benchmark)
    if source_errors:
        return [*details, *source_errors]
    if entities is None:
        details.append(
            Finding(
                "error",
                "available_source_index_trace_records needs source_index.json",
                location=str(artifact_path),
            )
        )
        return details

    for source_id, ref_loc in refs:
        if _is_planner_source_ref(source_id):
            details.append(
                Finding(
                    "error",
                    "available_source_index_trace_records must use source-index ids, not planner:*",
                    location=ref_loc,
                )
            )
            continue
        entity = entities.get(source_id)
        if entity is None:
            details.append(
                Finding(
                    "error",
                    f"available_source_index_trace_records references missing source_index id {source_id!r}",
                    location=ref_loc,
                )
            )
            continue
        if entity.get("selected") is not True or (
            entity.get("semantic_disposition") == "dropped"
        ):
            details.append(
                Finding(
                    "error",
                    f"available_source_index_trace_records references dropped/unselected source_index id {source_id!r}",
                    location=ref_loc,
                )
            )
        if _source_index_entity_is_template(entity):
            details.append(
                Finding(
                    "error",
                    f"available_source_index_trace_records id {source_id!r} is a generic macro template, not type-specific trace evidence",
                    location=ref_loc,
                )
            )
    return details


def _validate_trusted_call_chain_source_ids(
    benchmark: Path,
    artifact_data: dict,
    artifact_path: Path,
) -> list[Finding]:
    """Trusted callback call chains must be source-index traceable."""
    chain = artifact_data.get("trusted_call_chain")
    if not isinstance(chain, list):
        return []

    details: list[Finding] = []
    refs: list[tuple[str, str]] = []
    for idx, entry in enumerate(chain):
        entry_loc = f"{artifact_path}:trusted_call_chain[{idx}]"
        if not isinstance(entry, dict):
            details.append(
                Finding(
                    "error",
                    "trusted_call_chain entries must be objects with name and source_id",
                    location=entry_loc,
                )
            )
            continue
        if not isinstance(entry.get("name"), str) or not entry.get("name"):
            details.append(
                Finding(
                    "error",
                    "trusted_call_chain entry missing name",
                    location=entry_loc,
                )
            )
        source_id = entry.get("source_id")
        if not isinstance(source_id, str) or not source_id:
            details.append(
                Finding(
                    "error",
                    "trusted_call_chain entry missing source_id",
                    location=entry_loc,
                )
            )
            continue
        refs.append((source_id, entry_loc))

    if not refs:
        return details

    entities, source_errors = _load_source_index_entities_by_id(benchmark)
    if source_errors:
        return [*details, *source_errors]
    if entities is None:
        details.append(
            Finding(
                "error",
                "trusted_call_chain source_id validation needs source_index.json",
                location=str(artifact_path),
            )
        )
        return details

    for source_id, ref_loc in refs:
        if _is_planner_source_ref(source_id):
            details.append(
                Finding(
                    "error",
                    "trusted_call_chain source_id must be a source-index id, not planner:*",
                    location=ref_loc,
                )
            )
            continue
        entity = entities.get(source_id)
        if entity is None:
            details.append(
                Finding(
                    "error",
                    f"trusted_call_chain references missing source_index id {source_id!r}",
                    location=ref_loc,
                )
            )
            continue
        if entity.get("selected") is not True or (
            entity.get("semantic_disposition") == "dropped"
        ):
            details.append(
                Finding(
                    "error",
                    f"trusted_call_chain references dropped/unselected source_index id {source_id!r}",
                    location=ref_loc,
                )
            )
    return details


def check_policy_artifacts(benchmark: Path) -> CheckResult:
    """Validate plan-linked policy artifacts for trusted/representation gaps.

    Draft artifacts are useful curation evidence, but they must not silently
    clear promotion blockers. This check makes that boundary deterministic.
    """
    plan, plan_path, plan_errors = _load_plan(benchmark)
    if plan_errors:
        return CheckResult("policy_artifacts", "fail", plan_errors)
    if plan is None:
        return CheckResult(
            "policy_artifacts",
            "pass",
            [Finding("info", "no plan.json found; policy-artifact check inactive")],
        )

    details: list[Finding] = []
    refs_seen = 0
    artifact_records: list[dict[str, object]] = []
    artifacts_by_id: dict[str, list[dict[str, object]]] = {}
    for pkg_name, mod_name, collection, item in _iter_plan_items(plan):
        item_name = item.get("name") or item.get("lean_name") or "<unnamed>"
        location = f"plan:{pkg_name}.{mod_name}.{collection}.{item_name}"
        for artifact_kind, artifact_field, status_field in _POLICY_ARTIFACT_FIELDS:
            artifact_value = item.get(artifact_field)
            if not artifact_value:
                continue
            refs_seen += 1
            if not isinstance(artifact_value, str):
                details.append(
                    Finding(
                        "error",
                        f"{artifact_field} must be a relative artifact path string",
                        location=location,
                    )
                )
                continue

            artifact_path = _resolve_plan_artifact(benchmark, plan_path, artifact_value)
            if artifact_path is None:
                details.append(
                    Finding(
                        "error",
                        f"{artifact_kind} artifact not found or unsafe path: {artifact_value}",
                        location=location,
                    )
                )
                continue
            try:
                artifact_data = json.loads(artifact_path.read_text(encoding="utf-8"))
            except json.JSONDecodeError as e:
                details.append(
                    Finding(
                        "error",
                        f"{artifact_kind} artifact is not valid JSON: {e}",
                        location=str(artifact_path),
                    )
                )
                continue

            details.extend(
                _validate_available_source_index_trace_records(
                    benchmark, artifact_data, artifact_path
                )
            )

            artifact_status = artifact_data.get("status")
            plan_status = item.get(status_field)
            if not isinstance(artifact_status, str):
                details.append(
                    Finding(
                        "error",
                        f"{artifact_kind} artifact missing string status",
                        location=str(artifact_path),
                    )
                )
            elif isinstance(plan_status, str) and artifact_status != plan_status:
                details.append(
                    Finding(
                        "error",
                        f"{status_field}={plan_status!r} does not match artifact status={artifact_status!r}",
                        location=location,
                    )
                )

            id_key = (
                "requirement_id"
                if artifact_kind == "macro_expansion_requirement"
                else "policy_id"
            )
            artifact_id = artifact_data.get(id_key)
            if not isinstance(artifact_id, str):
                details.append(
                    Finding(
                        "error",
                        f"{artifact_kind} artifact missing string {id_key}",
                        location=str(artifact_path),
                    )
                )

            promotion_effect = artifact_data.get("promotion_effect")
            if not isinstance(promotion_effect, dict):
                details.append(
                    Finding(
                        "error",
                        f"{artifact_kind} artifact missing promotion_effect object",
                        location=str(artifact_path),
                    )
                )
            if artifact_kind == "trusted_boundary_policy":
                details.extend(
                    _validate_trusted_call_chain_source_ids(
                        benchmark, artifact_data, artifact_path
                    )
                )
                for required in ("trusted_call_chain", "trusted_assumptions"):
                    if not isinstance(artifact_data.get(required), list):
                        details.append(
                            Finding(
                                "error",
                                f"trusted boundary policy missing {required} list",
                                location=str(artifact_path),
                            )
                        )
                if not isinstance(artifact_data.get("test_policy"), dict):
                    details.append(
                        Finding(
                            "error",
                            "trusted boundary policy missing test_policy object",
                            location=str(artifact_path),
                        )
                    )
            elif artifact_kind == "representation_policy":
                if not isinstance(artifact_data.get("blocked_specs"), list):
                    details.append(
                        Finding(
                            "error",
                            "representation policy missing blocked_specs list",
                            location=str(artifact_path),
                        )
                    )
            elif artifact_kind == "macro_expansion_requirement":
                if not isinstance(
                    artifact_data.get("required_source_index_records"), list
                ):
                    details.append(
                        Finding(
                            "error",
                            "macro expansion requirement missing required_source_index_records list",
                            location=str(artifact_path),
                        )
                    )
                if _artifact_allows_clearance(artifact_status, promotion_effect):
                    details.extend(
                        _validate_macro_expansion_clearance_evidence(
                            benchmark, artifact_data, artifact_path
                        )
                    )

            if _status_indicates_blocked(artifact_status) or (
                _promotion_effect_forbids_clearance(promotion_effect)
            ):
                if not _item_retains_policy_blocker(item):
                    details.append(
                        Finding(
                            "error",
                            f"{artifact_kind} artifact is draft/blocked but {item_name} is not marked with unresolved bridge or blocker metadata",
                            location=location,
                        )
                    )

            record = {
                "id": artifact_id,
                "kind": artifact_kind,
                "path": artifact_path,
                "status": artifact_status,
                "data": artifact_data,
                "item": item,
                "item_name": item_name,
                "location": location,
            }
            artifact_records.append(record)
            if isinstance(artifact_id, str):
                artifacts_by_id.setdefault(artifact_id, []).append(record)

    for record in artifact_records:
        artifact_data = record["data"]
        if not isinstance(artifact_data, dict):
            continue
        depends_on = artifact_data.get("depends_on")
        if depends_on is None:
            continue
        path = record["path"]
        location = str(path) if isinstance(path, Path) else None
        if not isinstance(depends_on, list) or not all(
            isinstance(dep, str) for dep in depends_on
        ):
            details.append(
                Finding(
                    "error",
                    "policy artifact depends_on must be a list of policy/requirement ids",
                    location=location,
                )
            )
            continue
        item = record["item"]
        item_blocked = (
            _item_retains_policy_blocker(item) if isinstance(item, dict) else False
        )
        artifact_status = record["status"]
        artifact_blocked = _status_indicates_blocked(artifact_status)
        for dep_id in depends_on:
            dependency_records = artifacts_by_id.get(dep_id, [])
            if not dependency_records:
                details.append(
                    Finding(
                        "error",
                        f"policy artifact depends on unknown policy/requirement id {dep_id!r}",
                        location=location,
                    )
                )
                continue
            for dependency in dependency_records:
                dep_status = dependency["status"]
                if _status_indicates_blocked(dep_status) and (
                    not artifact_blocked or not item_blocked
                ):
                    details.append(
                        Finding(
                            "error",
                            f"policy artifact {record['id']!r} depends on blocked policy/requirement {dep_id!r} but the dependent artifact or owning plan item is not still blocked",
                            location=location,
                        )
                    )

    if refs_seen == 0:
        details.append(
            Finding(
                "info",
                "no trusted/representation/macro policy artifacts referenced in plan.json",
            )
        )
    elif not details:
        details.append(
            Finding(
                "info",
                f"validated {refs_seen} plan-linked policy artifact references",
            )
        )

    status = "fail" if any(f.severity == "error" for f in details) else "pass"
    return CheckResult("policy_artifacts", status, details)


_PLAN_SOURCE_ID_FIELDS = ("source_id",)
_PLAN_SOURCE_ID_LIST_FIELDS = ("source_dependency_ids", "source_relations_referenced")


def _is_planner_source_ref(value: str) -> bool:
    return value.startswith("planner:")


def _plan_source_refs(item: dict) -> list[tuple[str, str]]:
    refs: list[tuple[str, str]] = []
    for field in _PLAN_SOURCE_ID_FIELDS:
        value = item.get(field)
        if isinstance(value, str) and value:
            refs.append((field, value))
    for field in _PLAN_SOURCE_ID_LIST_FIELDS:
        value = item.get(field)
        if not value:
            continue
        if isinstance(value, list):
            refs.extend((field, ref) for ref in value if isinstance(ref, str) and ref)
        else:
            refs.append((field, f"<non-list:{value!r}>"))
    return refs


def check_plan_source_references(benchmark: Path) -> CheckResult:
    """Require plan source references to round-trip through source_index.json."""
    plan, _plan_path, plan_errors = _load_plan(benchmark)
    if plan_errors:
        return CheckResult("plan_source_references", "fail", plan_errors)
    if plan is None:
        return CheckResult(
            "plan_source_references",
            "pass",
            [
                Finding(
                    "info", "no plan.json found; plan source-reference check inactive"
                )
            ],
        )

    source_index, source_path, source_errors = _load_first_json(
        benchmark, ["source_index.json"]
    )
    if source_errors:
        return CheckResult("plan_source_references", "fail", source_errors)

    details: list[Finding] = []
    refs_seen = 0
    if source_index is None:
        for _pkg_name, _mod_name, _collection, item in _iter_plan_items(plan):
            refs_seen += len(
                [
                    ref
                    for _field, ref in _plan_source_refs(item)
                    if not _is_planner_source_ref(ref)
                ]
            )
        if refs_seen:
            return CheckResult(
                "plan_source_references",
                "fail",
                [
                    Finding(
                        "error",
                        f"plan.json contains {refs_seen} non-planner source reference(s) but no source_index.json was found",
                    )
                ],
            )
        return CheckResult(
            "plan_source_references",
            "pass",
            [Finding("info", "plan has no non-planner source references")],
        )

    entities = {
        str(entity.get("id")): entity
        for entity in _source_index_entities(source_index)
        if isinstance(entity, dict) and entity.get("id")
    }
    location = str(source_path) if source_path else "source_index.json"

    for pkg_name, mod_name, collection, item in _iter_plan_items(plan):
        item_name = item.get("name") or item.get("lean_name") or "<unnamed>"
        item_loc = f"plan:{pkg_name}.{mod_name}.{collection}.{item_name}"
        for field, ref in _plan_source_refs(item):
            if ref.startswith("<non-list:"):
                details.append(
                    Finding(
                        "error",
                        f"{field} must be a list of source_index ids",
                        location=item_loc,
                    )
                )
                continue
            if _is_planner_source_ref(ref):
                continue
            refs_seen += 1
            entity = entities.get(ref)
            if entity is None:
                details.append(
                    Finding(
                        "error",
                        f"{field} references missing source_index id {ref!r}",
                        location=item_loc,
                    )
                )
                continue
            if (
                entity.get("selected") is False
                or (entity.get("role") or entity.get("default_role"))
                == "dropped_with_reason"
            ):
                details.append(
                    Finding(
                        "error",
                        f"{field} references dropped/unselected source_index id {ref!r}",
                        location=item_loc,
                    )
                )

            source_file = item.get("source_file")
            if (
                field == "source_id"
                and isinstance(source_file, str)
                and source_file
                and source_file != entity.get("source_file")
            ):
                details.append(
                    Finding(
                        "error",
                        f"{item_name} source_file={source_file!r} does not match source_index[{ref!r}].source_file={entity.get('source_file')!r}",
                        location=item_loc,
                    )
                )
            source_line = item.get("source_line")
            if (
                field == "source_id"
                and isinstance(source_line, int)
                and isinstance(entity.get("source_line"), int)
                and source_line != entity.get("source_line")
            ):
                details.append(
                    Finding(
                        "error",
                        f"{item_name} source_line={source_line!r} does not match source_index[{ref!r}].source_line={entity.get('source_line')!r}",
                        location=item_loc,
                    )
                )

    if not details:
        details.append(
            Finding(
                "info",
                f"{refs_seen} plan source reference(s) round-trip through {location}",
            )
        )

    status = "fail" if any(f.severity == "error" for f in details) else "pass"
    return CheckResult("plan_source_references", status, details)


def check_semantic_weakening(benchmark: Path) -> CheckResult:
    """Require explicit review when source theorems are decomposed/weakened.

    Exploratory structural surrogates may be useful curation artifacts, but a
    promotion-scope spec must not be considered complete while it still carries
    unresolved bridge metadata.
    """
    manifest, errors = _load_manifest(benchmark)
    if manifest is None:
        return CheckResult("semantic_weakening", "fail", errors)
    plan, _plan_path, plan_errors = _load_plan(benchmark)
    if plan_errors:
        return CheckResult("semantic_weakening", "fail", plan_errors)

    details: list[Finding] = []
    saw_metadata = False
    for item, location in _semantic_items_from_plan_or_manifest(manifest, plan):
        if not isinstance(item, dict):
            continue
        source_theorem = item.get("source_theorem") or item.get("source_spec")
        decomposed = item.get("decomposes_source") or item.get("translated_specs")
        bridge = item.get("semantic_bridge_required") or item.get(
            "bridge_lemmas_required"
        )
        status = item.get("equivalence_status")
        if source_theorem or decomposed or bridge or status:
            saw_metadata = True
        if decomposed and not status:
            details.append(
                Finding(
                    "error",
                    f"{item.get('name', source_theorem)} decomposes a source theorem but lacks equivalence_status",
                    location=location,
                )
            )
        if decomposed and bridge == []:
            details.append(
                Finding(
                    "warn",
                    f"{item.get('name', source_theorem)} declares decomposition with no semantic bridge lemmas",
                    location=location,
                )
            )
        if status in {"weaker", "unclear"} and not (
            item.get("requires_human_review")
            or item.get("degrade_to_structural_surrogate")
            or item.get("review_status") == "approved"
        ):
            details.append(
                Finding(
                    "error",
                    f"{item.get('name', source_theorem)} has equivalence_status={status!r}; mark requires_human_review or degrade_to_structural_surrogate",
                    location=location,
                )
            )
        if item.get("promotion_scope") is True:
            blocker_reasons: list[str] = []
            if item.get("degrade_to_structural_surrogate"):
                blocker_reasons.append("degrade_to_structural_surrogate=true")
            if bridge:
                blocker_reasons.append("semantic_bridge_required is non-empty")
            promotion_status = item.get("promotion_status")
            if isinstance(promotion_status, str) and promotion_status.startswith(
                "blocked"
            ):
                blocker_reasons.append(f"promotion_status={promotion_status!r}")
            if blocker_reasons:
                details.append(
                    Finding(
                        "error",
                        f"{item.get('name', source_theorem)} is promotion-scope but still has unresolved semantic bridge metadata: {', '.join(blocker_reasons)}",
                        location=location,
                    )
                )

    if not saw_metadata:
        details.append(
            Finding(
                "info",
                "no semantic weakening metadata found; check is inactive for this benchmark",
            )
        )

    status = (
        "fail"
        if any(f.severity == "error" for f in details)
        else ("warn" if any(f.severity == "warn" for f in details) else "pass")
    )
    return CheckResult("semantic_weakening", status, details)


# ─────────────────────────────────────────────────────────────
# Check: placeholder helper/model bodies in plan


def check_plan_placeholder_bodies(benchmark: Path) -> CheckResult:
    """Reject frozen helper/model plan entries that encode fake semantics."""
    plan, _plan_path, plan_errors = _load_plan(benchmark)
    if plan_errors:
        return CheckResult("plan_placeholder_bodies", "fail", plan_errors)
    if plan is None:
        return CheckResult(
            "plan_placeholder_bodies",
            "pass",
            [Finding("info", "no plan.json found; placeholder-body check inactive")],
        )

    details = _plan_placeholder_semantics(plan)
    status = "fail" if any(f.severity == "error" for f in details) else "pass"
    if not details:
        details.append(Finding("info", "no fake helper/model placeholder bodies found"))
    return CheckResult("plan_placeholder_bodies", status, details)


# ─────────────────────────────────────────────────────────────
# Check: curation config credential hygiene


def check_config_hygiene(benchmark: Path) -> CheckResult:
    """Local Codex-auth curation configs must not persist API credentials."""
    path = _find_config_yaml(benchmark)
    if path is None:
        return CheckResult(
            "config_hygiene",
            "pass",
            [Finding("info", "no config.yaml found; config hygiene check inactive")],
        )
    try:
        data = yaml.safe_load(path.read_text(encoding="utf-8"))
    except yaml.YAMLError as e:
        return CheckResult(
            "config_hygiene",
            "fail",
            [
                Finding(
                    "error",
                    f"config.yaml is not valid YAML: {e}",
                    location=str(path),
                )
            ],
        )
    if not isinstance(data, dict):
        return CheckResult(
            "config_hygiene",
            "fail",
            [
                Finding(
                    "error",
                    "config.yaml must contain a mapping",
                    location=str(path),
                )
            ],
        )

    details: list[Finding] = []
    if data.get("agent_kind") == "codex" and data.get("codex_auth_mode") == "local":
        for field in ("api_key", "api_base_url"):
            if data.get(field) not in (None, ""):
                details.append(
                    Finding(
                        "error",
                        f"local Codex config must persist {field}=null",
                        location=str(path),
                    )
                )
    if details:
        return CheckResult("config_hygiene", "fail", details)
    return CheckResult(
        "config_hygiene",
        "pass",
        [Finding("info", "config.yaml hygiene ok", location=str(path))],
    )


# ─────────────────────────────────────────────────────────────
# Check 6: lake build


def check_build(benchmark: Path, timeout: int = 300) -> CheckResult:
    """Check 6: `lake build` succeeds from the benchmark directory."""
    try:
        r = subprocess.run(
            ["lake", "build"],
            cwd=benchmark,
            capture_output=True,
            text=True,
            timeout=timeout,
        )
    except FileNotFoundError:
        return CheckResult(
            "build",
            "warn",
            [Finding("warn", "`lake` binary not found; skipping build check")],
        )
    except subprocess.TimeoutExpired:
        return CheckResult(
            "build",
            "fail",
            [Finding("error", f"`lake build` timed out after {timeout}s")],
        )

    tail = (r.stderr or r.stdout).splitlines()[-8:]
    if r.returncode != 0:
        return CheckResult(
            "build",
            "fail",
            [
                Finding("error", "`lake build` failed"),
                Finding("info", "\n".join(tail)),
            ],
        )
    return CheckResult("build", "pass", [Finding("info", "\n".join(tail))])


# ─────────────────────────────────────────────────────────────
# Check 7: #guard tests


_GUARD_RE = re.compile(r"^\s*#guard\b")
_BLOCK_COMMENT_OPEN_RE = re.compile(r"/-")
_BLOCK_COMMENT_CLOSE_RE = re.compile(r"-/")


def _strip_block_comments(text: str) -> str:
    """Strip Lean ``/- ... -/`` block comments (handles nesting)."""
    out: list[str] = []
    i = 0
    depth = 0
    n = len(text)
    while i < n:
        if text.startswith("/-", i):
            depth += 1
            i += 2
            continue
        if depth > 0 and text.startswith("-/", i):
            depth -= 1
            i += 2
            # Replace the comment span with a single newline so line numbers
            # roughly align (we don't track them precisely, just enough so the
            # `\s*#guard` regex still anchors at line starts).
            continue
        if depth == 0:
            out.append(text[i])
        elif text[i] == "\n":
            out.append("\n")
        i += 1
    return "".join(out)


def _guard_only_text(code_text: str) -> str:
    """Return text inside #guard assertions, including multi-line guards."""
    guard_chunks: list[str] = []
    current: list[str] = []
    in_guard = False
    stop_prefixes = (
        "#check",
        "#eval",
        "abbrev ",
        "axiom ",
        "def ",
        "example ",
        "import ",
        "inductive ",
        "instance ",
        "namespace ",
        "opaque ",
        "open ",
        "structure ",
        "theorem ",
    )
    for line in code_text.splitlines():
        stripped = line.lstrip()
        top_level = line == stripped
        if _GUARD_RE.match(line):
            if current:
                guard_chunks.append("\n".join(current))
            current = [line]
            in_guard = True
            continue
        if not in_guard:
            continue
        if top_level and stripped.startswith(stop_prefixes):
            guard_chunks.append("\n".join(current))
            current = []
            in_guard = False
            continue
        current.append(line)
    if current:
        guard_chunks.append("\n".join(current))
    return "\n".join(guard_chunks)


def check_guards(benchmark: Path) -> CheckResult:
    """Check 7: Test.lean exists and has #guard assertions covering manifest APIs."""
    manifest, errors = _load_manifest(benchmark)
    if manifest is None:
        return CheckResult("guards", "fail", errors)

    test_rel = manifest.get("files", {}).get("test")
    if not test_rel:
        return CheckResult(
            "guards",
            "fail",
            [
                Finding("error", "manifest files.test not set"),
            ],
        )
    test_path = _abs(benchmark, test_rel)
    if not test_path.exists():
        return CheckResult(
            "guards",
            "fail",
            [
                Finding("error", f"test file missing: {test_rel}", location=test_rel),
            ],
        )
    text = _strip_block_comments(test_path.read_text())
    code_text = "\n".join(line.split("--", 1)[0] for line in text.splitlines())
    # Also strip line comments anchored at the `#guard` position (`-- #guard …`
    # is text noise, not a real assertion).
    count = sum(
        1
        for line in code_text.splitlines()
        if _GUARD_RE.match(line) and not line.lstrip().startswith("--")
    )
    if count == 0:
        return CheckResult(
            "guards",
            "fail",
            [
                Finding(
                    "error", f"{test_rel} has no #guard assertions", location=test_rel
                ),
            ],
        )
    guard_text = _guard_only_text(code_text)
    api_names: list[str] = []
    for pkg in manifest.get("packages", []):
        for mod in pkg.get("modules", []):
            for api in mod.get("apis", []):
                if api.get("kind", "api") != "api":
                    continue
                if name := api.get("name"):
                    api_names.append(name)

    missing_apis: list[str] = []
    for name in api_names:
        tail = name.rsplit(".", 1)[-1]
        if not re.search(rf"(?<![\w?!']){re.escape(tail)}(?![\w?!'])", guard_text):
            missing_apis.append(name)

    details = [
        Finding("info", f"{count} #guard assertion(s) in {test_rel}"),
    ]
    if missing_apis:
        details.append(
            Finding(
                "warn",
                f"{len(missing_apis)} manifest API(s) are not mentioned in {test_rel}: "
                f"{missing_apis[:10]}" + (" ..." if len(missing_apis) > 10 else ""),
                location=test_rel,
            )
        )

    return CheckResult(
        "guards",
        "warn" if missing_apis else "pass",
        details,
    )


# ─────────────────────────────────────────────────────────────
# Check 8: toolchain match


def check_toolchain(benchmark: Path) -> CheckResult:
    """Check 8: lean-toolchain content matches manifest.lean_version."""
    manifest, errors = _load_manifest(benchmark)
    if manifest is None:
        return CheckResult("toolchain", "fail", errors)

    lv = manifest.get("lean_version")
    toolchain_path = benchmark / "lean-toolchain"
    if not toolchain_path.exists():
        return CheckResult(
            "toolchain",
            "fail",
            [
                Finding("error", "lean-toolchain file missing"),
            ],
        )
    declared = toolchain_path.read_text().strip()
    # Normalize: declared may be like "leanprover/lean4:v4.29.1"
    expected = f"leanprover/lean4:v{lv}" if lv else None
    if expected and declared != expected:
        return CheckResult(
            "toolchain",
            "fail",
            [
                Finding(
                    "error", f"lean-toolchain={declared!r} != manifest={expected!r}"
                ),
            ],
        )
    return CheckResult(
        "toolchain",
        "pass",
        [
            Finding("info", f"toolchain={declared}"),
        ],
    )


# ─────────────────────────────────────────────────────────────
# Top-level runner


_ALL_CHECKS = [
    ("manifest_schema", check_manifest_schema),
    ("manifest_vs_code", check_manifest_vs_code),
    ("markers_grammar", check_markers_grammar),
    ("markers_positioning", check_markers_positioning),
    ("file_roles", check_file_roles),
    ("spec_shape", lambda b: check_spec_shape(b)),
    ("spec_quality", lambda b: check_spec_quality(b)),
    ("source_alignment", lambda b: check_source_alignment(b)),
    ("api_spec_coverage", lambda b: check_api_spec_coverage(b)),
    ("provenance", lambda b: check_provenance(b)),
    ("trusted_boundary", lambda b: check_trusted_boundary(b)),
    ("source_index", lambda b: check_source_index(b)),
    ("source_coverage", lambda b: check_source_coverage(b)),
    ("entity_roles", lambda b: check_entity_roles(b)),
    ("reference_consistency", lambda b: check_reference_consistency(b)),
    ("trusted_surface", lambda b: check_trusted_surface(b)),
    ("import_delta", lambda b: check_import_delta(b)),
    ("policy_artifacts", lambda b: check_policy_artifacts(b)),
    ("plan_source_references", lambda b: check_plan_source_references(b)),
    ("semantic_weakening", lambda b: check_semantic_weakening(b)),
    ("plan_placeholder_bodies", lambda b: check_plan_placeholder_bodies(b)),
    ("config_hygiene", lambda b: check_config_hygiene(b)),
    ("guards", check_guards),
    ("toolchain", check_toolchain),
    # build is last (slowest, may be skipped)
]


def run_rule_checks(
    benchmark: Path,
    *,
    skip_build: bool = False,
    build_timeout: int = 300,
) -> dict[str, CheckResult]:
    """Run all rule-based checks and return {name: CheckResult}.

    Hard-stop semantics: when ``manifest_schema`` fails, the downstream
    checks (``manifest_vs_code``, ``markers_grammar``, ``markers_positioning``,
    ``file_roles``, ``spec_shape``, ``source_coverage``, ``guards``) become
    meaningless — they enumerate Lean files via ``manifest.packages[]`` and
    silently report ``pass`` when that's empty. Mark them ``skipped`` instead
    of letting them produce false positives. ``toolchain`` and ``build`` still
    run since they don't depend on the manifest's package structure.
    """
    results: dict[str, CheckResult] = {}
    schema_result = check_manifest_schema(benchmark)
    results["manifest_schema"] = schema_result
    schema_blocked = schema_result.status == "fail"
    skipped_msg = (
        "skipped: manifest_schema failed; downstream checks need a valid manifest"
    )
    for name, fn in _ALL_CHECKS:
        if name == "manifest_schema":
            continue
        if schema_blocked and name in _SCHEMA_DEPENDENT:
            results[name] = CheckResult(name, "skipped", [Finding("info", skipped_msg)])
        else:
            results[name] = fn(benchmark)
    if not skip_build:
        results["build"] = check_build(benchmark, timeout=build_timeout)
    return results


_SCHEMA_DEPENDENT = frozenset(
    {
        "manifest_vs_code",
        "markers_grammar",
        "markers_positioning",
        "file_roles",
        "spec_shape",
        "spec_quality",
        "api_spec_coverage",
        "provenance",
        "trusted_boundary",
        "source_index",
        "source_coverage",
        "entity_roles",
        "reference_consistency",
        "trusted_surface",
        "import_delta",
        "policy_artifacts",
        "plan_source_references",
        "semantic_weakening",
        "plan_placeholder_bodies",
        "guards",
    }
)
