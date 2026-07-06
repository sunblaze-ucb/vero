"""Pre-agent-gen stage — materialize per-mode ``Proof/`` from curated tree.

Deterministic, pure-Python translation from the curation-stage output
(``manifest.json`` + ``Spec/*``) into a mode-specific ``Proof/`` layer:

* ``proof`` mode      — per spec: ``prove_S`` + ``disprove_S`` stubs.
* ``codeproof`` mode  — per spec: ``prove_S`` + ``unsat_S`` + ``sat_S``
  stubs, plus one dormant ``Proof/Joint.lean`` slot using the
  ``!solution`` marker.

Schema: see ``docs/pipeline-schema.md`` (``manifest.json``) and the
reference illustrations at ``reference/BankLedger/BankLedger/Proof_modeproof/``
and ``reference/BankLedger/BankLedger/Proof_modecodeproof/``.
"""

from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path
from typing import Literal

from vero.generation.benchmark import manifest_spec_name

Mode = Literal["proof", "codeproof"]

_JOINT_SLOT_NAME = "joint_unsatisfiability"


def _lean_module_suffix(module_name: str) -> str:
    return module_name.replace("/", ".")


@dataclass
class Module:
    package: str
    name: str
    # None for opaque / vocabulary-only modules (no Spec/*.lean file).
    spec_path: str | None
    specs: list[str]


@dataclass
class MaterializeResult:
    mode: Mode
    files_written: list[Path]


# ─────────────────────────────────────────────────────────────
# Manifest reading


def _load_manifest(benchmark: Path) -> dict:
    path = benchmark / "manifest.json"
    if not path.exists():
        raise FileNotFoundError(f"manifest.json not found at {path}")
    return json.loads(path.read_text())


def _iter_modules(manifest: dict) -> list[Module]:
    out: list[Module] = []
    for pkg in manifest.get("packages", []):
        for mod in pkg.get("modules", []):
            out.append(
                Module(
                    package=pkg["name"],
                    name=mod["name"],
                    spec_path=mod.get("spec"),
                    specs=[manifest_spec_name(spec) for spec in mod.get("specs", [])],
                )
            )
    return out


# ─────────────────────────────────────────────────────────────
# File templates


def _module_header_proof_mode(package: str, module_name: str) -> str:
    module_import = _lean_module_suffix(module_name)
    return f"""\
import {package}.Harness
import {package}.Spec.{module_import}

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# {package}.Proof.{module_import} (proof mode)

Pre-generated theorem stubs. Per spec S: `prove_S` + `disprove_S`.
LLM fills exactly one of each pair; the other stays as `sorry`.

DO NOT MODIFY theorem statements. Fill only the `sorry` proof bodies.
-/

-- !benchmark @start global_aux
-- !benchmark @end global_aux
"""


def _module_header_codeproof_mode(package: str, module_name: str) -> str:
    module_import = _lean_module_suffix(module_name)
    return f"""\
import {package}.Harness
import {package}.Spec.{module_import}

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# {package}.Proof.{module_import} (codeproof mode)

Pre-generated theorem stubs. Per spec S:
- `prove_S : spec_S canonical`
- `unsat_S : ¬ ∃ impl : RepoImpl, spec_S impl`
- `sat_S   : ∃ impl : RepoImpl, spec_S impl`

LLM fills exactly one body per spec. The `sat_S` case is paired
with S listed in the `!solution` block in `Proof/Joint.lean`.

DO NOT MODIFY theorem statements. Fill only the `sorry` proof bodies.
-/

-- !benchmark @start global_aux
-- !benchmark @end global_aux
"""


def _proof_stub_block(
    *,
    def_name: str,
    kind: str,
    target_spec: str,
    theorem_line: str,
) -> str:
    """Emit `proof_aux` + theorem + `proof` marker wrapping `sorry`."""
    return f"""\

-- !benchmark @start proof_aux def={def_name}
-- !benchmark @end proof_aux def={def_name}

{theorem_line}
-- !benchmark @start proof def={def_name} kind={kind} target={target_spec}
  sorry
-- !benchmark @end proof def={def_name}
"""


def _module_body_proof_mode(specs: list[str]) -> str:
    out = []
    for spec in specs:
        bare = spec[len("spec_") :] if spec.startswith("spec_") else spec
        out.append(f"\n-- ── {spec} ──")
        out.append(
            _proof_stub_block(
                def_name=f"prove_{bare}",
                kind="prove",
                target_spec=spec,
                theorem_line=f"theorem prove_{bare} : {spec} canonical := by",
            )
        )
        out.append(
            _proof_stub_block(
                def_name=f"disprove_{bare}",
                kind="disprove",
                target_spec=spec,
                theorem_line=f"theorem disprove_{bare} : ¬ {spec} canonical := by",
            )
        )
    return "".join(out)


def _module_body_codeproof_mode(specs: list[str]) -> str:
    out = []
    for spec in specs:
        bare = spec[len("spec_") :] if spec.startswith("spec_") else spec
        out.append(f"\n-- ── {spec} ──")
        out.append(
            _proof_stub_block(
                def_name=f"prove_{bare}",
                kind="prove",
                target_spec=spec,
                theorem_line=f"theorem prove_{bare} : {spec} canonical := by",
            )
        )
        out.append(
            _proof_stub_block(
                def_name=f"unsat_{bare}",
                kind="unsat",
                target_spec=spec,
                theorem_line=f"theorem unsat_{bare} : ¬ ∃ impl : RepoImpl, {spec} impl := by",
            )
        )
        out.append(
            _proof_stub_block(
                def_name=f"sat_{bare}",
                kind="sat",
                target_spec=spec,
                theorem_line=f"theorem sat_{bare} : ∃ impl : RepoImpl, {spec} impl := by",
            )
        )
    return "".join(out)


def _joint_lean(root_package: str, spec_imports: list[str]) -> str:
    imports = "\n".join(
        f"import {root_package}.Spec.{_lean_module_suffix(m)}" for m in spec_imports
    )
    return f"""\
import {root_package}.Harness
{imports}

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# {root_package}.Proof.Joint (codeproof mode)

Workspace for the single joint-unsatisfiability claim per benchmark.
One slot, named `{_JOINT_SLOT_NAME}`. Paired with `sat_S` theorems
in `Proof/<Module>.lean` files: a spec S named in the `!solution`
below must also have its `sat_S` body proved.

Multi-package benchmarks still have exactly ONE Joint.lean / one
slot. Specs from any package appear in the same `!solution` list
(fully qualified if namespaced).

If the LLM does not wish to claim any joint-unsat, leave all blocks
commented / unfilled; the file remains compile-clean.

Evaluator: reads the spec list from `!solution` (rejects duplicates),
reads the proof body from `!benchmark proof`, rerenders
`joint_unsat <specs> by <body>`. The LLM's own `claim` content is
discarded.
-/

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- ── The one joint-unsat slot ─────────────────────────────

-- !solution @start def={_JOINT_SLOT_NAME} kind=joint_unsat
-- specs=[<FILL: comma-separated spec names, e.g. spec_a, spec_b>]
-- !solution @end def={_JOINT_SLOT_NAME} kind=joint_unsat

-- !benchmark @start proof_aux def={_JOINT_SLOT_NAME}
-- !benchmark @end proof_aux def={_JOINT_SLOT_NAME}

-- !benchmark @start claim def={_JOINT_SLOT_NAME} kind=joint_unsat
-- joint_unsat <specs> by
-- !benchmark @end claim def={_JOINT_SLOT_NAME}

-- !benchmark @start proof def={_JOINT_SLOT_NAME} kind=joint_unsat
-- sorry
-- !benchmark @end proof def={_JOINT_SLOT_NAME}
"""


# ─────────────────────────────────────────────────────────────
# Public API


def materialize_proof(
    benchmark: Path,
    *,
    mode: Mode,
    dry_run: bool = False,
) -> MaterializeResult:
    """Materialize ``<Package>/Proof/<Module>.lean`` for every module in the manifest.

    For ``codeproof`` mode, additionally emit
    ``<root_package>/Proof/Joint.lean`` with one dormant joint-unsat slot.

    Returns the list of file paths that were written (or would be, if
    ``dry_run=True``).
    """
    manifest = _load_manifest(benchmark)
    root_package = manifest.get("root_package")
    modules = _iter_modules(manifest)

    written: list[Path] = []

    for mod in modules:
        # No specs ⇒ no proof stubs needed, and importing the non-existent
        # Spec/<name>.lean would fail to compile anyway.
        if not mod.specs:
            continue
        proof_dir = benchmark / mod.package / "Proof"
        proof_path = proof_dir / f"{mod.name}.lean"

        if mode == "proof":
            header = _module_header_proof_mode(mod.package, mod.name)
            body = _module_body_proof_mode(mod.specs)
        else:
            header = _module_header_codeproof_mode(mod.package, mod.name)
            body = _module_body_codeproof_mode(mod.specs)

        content = header + body
        if not dry_run:
            proof_path.parent.mkdir(parents=True, exist_ok=True)
            proof_path.write_text(content, encoding="utf-8")
        written.append(proof_path)

    if mode == "codeproof":
        joint_dir = benchmark / root_package / "Proof"
        joint_path = joint_dir / "Joint.lean"
        spec_modules = [
            m.name for m in modules if m.package == root_package and m.specs
        ]
        content = _joint_lean(root_package, spec_modules)
        if not dry_run:
            joint_dir.mkdir(parents=True, exist_ok=True)
            joint_path.write_text(content, encoding="utf-8")
        written.append(joint_path)

    return MaterializeResult(mode=mode, files_written=written)
