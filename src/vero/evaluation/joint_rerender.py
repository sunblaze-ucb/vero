"""Joint-unsat re-render (codeproof only).

Anti-cheat: the LLM's ``!benchmark claim`` content is discarded. The evaluator reads:

- ``!solution specs=[spec_a, spec_b, …]`` from ``Proof/Joint.lean``
- ``!benchmark @start proof def=joint_unsatisfiability`` body
- ``!benchmark @start proof_aux def=joint_unsatisfiability`` body (if any)
- ``!benchmark @start imports`` body (if any, for extra imports)
- ``!benchmark @start global_aux`` body (if any)

…and writes a fresh ``eval/JointCheck.lean`` file that re-invokes the ``joint_unsat`` macro from the extracted spec list + extracted body. Compiling this file with ``lake lean`` tells us:

- ``JOINT_NO_CLAIM`` — solution block holds the default ``<FILL: …>`` placeholder; no claim made (legitimate).
- ``JOINT_DUPLICATE`` — spec list contains duplicates (anti-cheat).
- ``JOINT_BAD_LIST`` — spec list doesn't parse cleanly.
- ``JOINT_BUILD_ERROR`` — macro invocation or body didn't compile.
- ``JOINT_SORRY`` — compiled but the generated theorem depends on ``sorryAx``.
- ``JOINT_OK`` — compiled, no sorry, no user axioms.
"""

from __future__ import annotations

import re
from dataclasses import dataclass, field
from pathlib import Path
from typing import Literal

from vero.evaluation.lake import lean_run_file
from vero.generation.benchmark import Benchmark
from vero.generation.extractor import (
    Artifact,
    proof_slot,
    slots_by,
    solution_slot,
)

JointStatus = Literal[
    "no_claim",
    "duplicate",
    "bad_list",
    "build_error",
    "sorry",
    "user_axiom",
    "ok",
]


@dataclass
class JointRerenderResult:
    status: JointStatus
    specs: tuple[str, ...] = ()
    theorem_name: str | None = None
    axioms: list[str] = field(default_factory=list)
    notes: str = ""


_PLACEHOLDER = re.compile(r"<\s*FILL\b", re.IGNORECASE)
_LIST_RE = re.compile(r"specs\s*=\s*\[(?P<inner>[^\]]*)\]")


def _parse_spec_list(solution_body: list[str]) -> tuple[str, ...] | None:
    """Extract the ``specs=[…]`` list from the solution block body lines.

    Accepts either a single line ``specs=[a, b]`` or multi-line (rare).
    Returns None if no list is found or if the placeholder is still present.
    """
    text = "\n".join(solution_body)
    if _PLACEHOLDER.search(text):
        return None
    m = _LIST_RE.search(text)
    if not m:
        return None
    inner = m.group("inner").strip()
    if not inner:
        return ()
    parts = [p.strip() for p in inner.split(",")]
    parts = [p for p in parts if p]
    return tuple(parts)


def _spec_to_module(bench: Benchmark, spec: str) -> str | None:
    for m in bench.iter_modules():
        if spec in m.specs:
            return m.name
    return None


def _render_joint_check(
    bench: Benchmark,
    specs: tuple[str, ...],
    *,
    proof_body: list[str],
    proof_aux_body: list[str],
    global_aux_body: list[str],
    imports_body: list[str],
) -> tuple[str, str]:
    """Render the ``eval/JointCheck.lean`` file contents + generated theorem name."""
    pkg = bench.root_package
    needed_modules = {m for s in specs if (m := _spec_to_module(bench, s)) is not None}
    # Import only what's needed to re-render ``joint_unsat``: the harness
    # (macro + RepoImpl) and the spec files for the named specs. Do NOT
    # import ``<pkg>.Proof`` — that would drag in the LLM's own Joint.lean
    # claim (a twin definition of the same theorem → name collision).
    import_lines = [f"import {pkg}.Harness"]
    for m in sorted(needed_modules):
        import_lines.append(f"import {pkg}.Spec.{m}")

    lines: list[str] = list(import_lines) + [""]

    if imports_body:
        lines.extend(imports_body)
        lines.append("")

    if global_aux_body:
        lines.extend(global_aux_body)
        lines.append("")

    if proof_aux_body:
        lines.extend(proof_aux_body)
        lines.append("")

    thm_name = "joint_unsat." + ".".join(specs)
    specs_str = " ".join(specs)
    lines.append(f"joint_unsat {specs_str} by")
    # Indent each body line by 2 spaces ONLY if not already indented at all.
    # Simpler: pass through verbatim — tactic blocks in Lean accept arbitrary indent
    # as long as it's consistent and greater than the `by` column.
    for ln in proof_body:
        lines.append(ln)
    lines.append("")
    lines.append(f"#print axioms {thm_name}")

    return ("\n".join(lines) + "\n", thm_name)


def rerender_joint(
    sandbox_dir: Path,
    artifact: Artifact,
    *,
    timeout: int = 600,
) -> JointRerenderResult:
    """Extract + re-render + compile the codeproof joint-unsat slot."""
    sandbox_dir = Path(sandbox_dir).resolve()
    bench = Benchmark(sandbox_dir)

    sol = solution_slot(artifact, "joint_unsatisfiability")
    proof = proof_slot(artifact, "joint_unsatisfiability")
    if sol is None or proof is None or not sol.found or not proof.found:
        return JointRerenderResult(
            status="no_claim",
            notes="missing !solution or !benchmark proof slot for joint_unsatisfiability",
        )

    specs = _parse_spec_list(sol.body_lines)
    if specs is None:
        return JointRerenderResult(
            status="no_claim",
            notes="solution block is the default placeholder",
        )
    if len(specs) != len(set(specs)):
        return JointRerenderResult(
            status="duplicate", specs=specs, notes="spec list contains duplicates"
        )
    if len(specs) < 2:
        return JointRerenderResult(
            status="bad_list",
            specs=specs,
            notes="joint_unsat requires at least 2 specs",
        )
    known = {s for m in bench.iter_modules() for s in m.specs}
    unknown = [s for s in specs if s not in known]
    if unknown:
        return JointRerenderResult(
            status="bad_list",
            specs=specs,
            notes=f"unknown specs: {unknown!r}",
        )
    # Is the proof body a placeholder sorry-comment? If so, no claim.
    body_non_comment = [
        ln for ln in proof.body_lines if ln.strip() and not ln.lstrip().startswith("--")
    ]
    if not body_non_comment:
        return JointRerenderResult(
            status="no_claim", specs=specs, notes="proof body is commented/empty"
        )

    # Gather companion file-level bodies from the same file.
    joint_file = bench.joint_file_path()
    imports_body: list[str] = []
    global_aux_body: list[str] = []
    proof_aux_body: list[str] = []
    for s in slots_by(artifact, prefix="benchmark"):
        if Path(sandbox_dir / s.file) != joint_file:
            continue
        if s.key == "imports":
            imports_body = s.body_lines
        elif s.key == "global_aux":
            global_aux_body = s.body_lines
        elif s.key == "proof_aux" and s.def_name == "joint_unsatisfiability":
            proof_aux_body = s.body_lines

    content, thm = _render_joint_check(
        bench,
        specs,
        proof_body=proof.body_lines,
        proof_aux_body=proof_aux_body,
        global_aux_body=global_aux_body,
        imports_body=imports_body,
    )

    eval_dir = sandbox_dir / "eval"
    eval_dir.mkdir(exist_ok=True)
    check_file = eval_dir / "JointCheck.lean"
    check_file.write_text(content, encoding="utf-8")

    # The rendered file ends with ``#print axioms <thm>``. Running it with
    # ``lake lean`` gives us both compile success/failure AND the axiom
    # report in one shot; parse the axiom line directly from the output.
    res = lean_run_file(sandbox_dir, check_file, timeout=timeout)
    if res.exit_code != 0:
        return JointRerenderResult(
            status="build_error",
            specs=specs,
            theorem_name=thm,
            notes=res.combined[-1200:],
        )

    from vero.evaluation.axioms import _parse_axioms_output

    trusted = frozenset(bench.trusted_axioms) if bench.trusted_axioms else None
    [ax] = _parse_axioms_output(res.combined, [thm], trusted_axioms=trusted)
    if ax.status == "uses_sorry":
        return JointRerenderResult(
            status="sorry", specs=specs, theorem_name=thm, axioms=ax.axioms
        )
    if ax.status == "uses_user_axiom":
        return JointRerenderResult(
            status="user_axiom", specs=specs, theorem_name=thm, axioms=ax.axioms
        )
    if ax.status == "clean":
        return JointRerenderResult(
            status="ok", specs=specs, theorem_name=thm, axioms=ax.axioms
        )
    return JointRerenderResult(
        status="build_error",
        specs=specs,
        theorem_name=thm,
        notes=f"axiom check returned status={ax.status}; tail: {res.combined[-600:]}",
    )
