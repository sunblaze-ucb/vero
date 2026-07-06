"""Axiom inspection via ``#print axioms``.

Given a list of fully-qualified theorem names to check, we synthesize one Lean file per proof module under ``<sandbox>/eval/AxiomCheck_<pkg>_Proof_<Module>.lean`` that imports exactly that one proof module and emits ``#print axioms <name>`` per theorem. Compiling the file with ``lake lean`` produces either:

- ``'<thm>' depends on axioms: [Classical.choice, propext, Quot.sound]``
- ``'<thm>' does not depend on any axioms``
- Includes ``sorryAx`` if the proof uses ``sorry``.

We parse the output per-theorem and classify each as ``clean | uses_sorry | uses_user_axiom | build_error | missing``. User axioms are anything outside the standard trio ``Classical.choice``, ``propext``, ``Quot.sound`` (plus ``sorryAx``, which we flag separately).

Curators can extend the allowlist via ``manifest.trusted_axioms`` — fully-qualified names listed there are unioned with the standard trio when classifying, so proofs that depend on e.g. a user-declared classical-reasoning helper grade as ``clean`` rather than ``uses_user_axiom``.
"""

from __future__ import annotations

import re
from dataclasses import dataclass, field
from pathlib import Path
from typing import Literal

from vero.evaluation.lake import LakeResult, lean_run_file

AxiomStatus = Literal[
    "clean",  # no axioms beyond the allowlist
    "uses_sorry",  # depends on sorryAx
    "uses_user_axiom",  # depends on some user axiom
    "build_error",  # file failed to compile
    "missing",  # axiom check didn't find the theorem at all
]

_STANDARD = frozenset({"Classical.choice", "propext", "Quot.sound"})


def _axiom_file_tag(proof_import: str) -> str:
    return proof_import.replace(".", "_").replace("/", "_")


def _allowed(trusted_axioms: frozenset[str] | None) -> frozenset[str]:
    """Standard trio ∪ curator-declared trusted axioms."""
    if trusted_axioms is None:
        return _STANDARD
    return _STANDARD | trusted_axioms


# Match either of:
# - "'Foo.bar' depends on axioms: [...]"   (axs may span multiple lines —
#   Lean's pretty-printer wraps long axiom lists)
# - "'Foo.bar' does not depend on any axioms"
#
# Run via finditer over the whole output (not splitlines) so the bracketed
# axiom list can include newlines without breaking the match.
_BLOCK = re.compile(
    r"'(?P<name>[^'\n]+)'\s+(?:depends on axioms:\s*\[(?P<axs>[^\]]*)\]|does not depend on any axioms\.?)"
)


@dataclass
class AxiomCheckResult:
    theorem: str
    status: AxiomStatus
    axioms: list[str] = field(default_factory=list)
    notes: str = ""


def _write_axiom_check_file(
    sandbox_dir: Path, theorems: list[str], *, proof_import: str
) -> Path:
    """Return the path of a freshly-written axiom-check Lean file.

    File name derived from ``proof_import`` so per-module checks don't
    clobber each other when run back-to-back.
    """
    eval_dir = sandbox_dir / "eval"
    eval_dir.mkdir(exist_ok=True)
    lines = [
        f"import {proof_import}",
        "",
    ]
    for thm in theorems:
        lines.append(f"#print axioms {thm}")
    content = "\n".join(lines) + "\n"
    tag = _axiom_file_tag(proof_import)
    out = eval_dir / f"AxiomCheck_{tag}.lean"
    out.write_text(content, encoding="utf-8")
    return out


def _parse_axioms_output(
    output: str,
    theorems: list[str],
    *,
    trusted_axioms: frozenset[str] | None = None,
) -> list[AxiomCheckResult]:
    """Parse ``#print axioms`` output per theorem. One result per requested name."""
    allowed = _allowed(trusted_axioms)
    # Map theorem (last segment) → result object
    results: dict[str, AxiomCheckResult] = {}
    for t in theorems:
        results[t] = AxiomCheckResult(theorem=t, status="missing")

    for m in _BLOCK.finditer(output):
        name = m.group("name").strip()
        # Map to the theorem this refers to. The requester usually passes a
        # bare (last-segment) name like "prove_create_exists"; Lean typically
        # reports the fully-qualified form like
        # "BankLedger.Proof.Account.prove_create_exists". Match in both
        # directions, exact first.
        key = None
        if name in results:
            key = name
        else:
            for t in results:
                if t == name or name.endswith("." + t) or t.endswith("." + name):
                    key = t
                    break
        if key is None:
            continue
        axs_raw = m.group("axs")
        if axs_raw is None:
            results[key].status = "clean"
            results[key].axioms = []
            continue
        # Lean wraps long axiom lists across lines with leading whitespace;
        # collapse newlines to spaces before splitting on commas.
        axs = [a.strip() for a in axs_raw.replace("\n", " ").split(",") if a.strip()]
        results[key].axioms = axs
        if "sorryAx" in axs:
            results[key].status = "uses_sorry"
        elif any(a not in allowed for a in axs):
            results[key].status = "uses_user_axiom"
        else:
            results[key].status = "clean"

    return [results[t] for t in theorems]


def check_axioms(
    sandbox_dir: Path,
    theorems: list[str],
    *,
    proof_import: str,
    timeout: int = 600,
    trusted_axioms: frozenset[str] | None = None,
) -> tuple[list[AxiomCheckResult], LakeResult]:
    """Write the axiom-check file, run lean on it, parse outputs.

    ``trusted_axioms``, if provided, extends the standard allowlist —
    proofs depending on those names grade as ``clean``.
    """
    sandbox_dir = Path(sandbox_dir).resolve()
    if not theorems:
        return ([], LakeResult(exit_code=0, stdout="", stderr="", combined=""))
    path = _write_axiom_check_file(sandbox_dir, theorems, proof_import=proof_import)
    res = lean_run_file(sandbox_dir, path, timeout=timeout)
    parsed = _parse_axioms_output(res.combined, theorems, trusted_axioms=trusted_axioms)
    if res.exit_code != 0:
        # File failed to compile — mark everything that didn't produce a result as build_error.
        for r in parsed:
            if r.status == "missing":
                r.status = "build_error"
                r.notes = "file did not compile"
    return parsed, res
