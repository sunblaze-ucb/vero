"""Per-spec grading + overall aggregation."""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Literal

from vero.evaluation.axioms import AxiomCheckResult
from vero.generation.benchmark import Benchmark, Module
from vero.generation.extractor import Artifact, slots_by

SpecStatus = Literal[
    "passed",  # exactly the expected fillings, clean axioms, compiles
    "unfilled",  # no slot was filled
    "overfilled",  # more slots filled than the mode allows (ambiguous intent)
    "sorry_leaked",  # a filled slot still depends on sorryAx
    "axiom_leaked",  # non-standard user axiom used
    "slot_body_tainted",  # filled slot syntactically contains axiom/admit tokens
    "build_error",  # file didn't compile / axiom check reports missing
    "unpaired_sat",  # sat_<S> filled but no verified joint_unsat claim names S
    "unsafe_keyword",  # agent-editable file contains `unsafe` — whole run voided
    "impl_oracle",  # agent impl uses `@[implemented_by]` (spec-oracle hack) — whole run voided
]


@dataclass
class KindResult:
    kind: str  # e.g. "prove", "disprove", "unsat", "sat"
    thm_name: str
    filled: bool
    axiom_status: str  # AxiomStatus value from AxiomCheckResult
    axioms: list[str] = field(default_factory=list)
    # Non-empty iff the filled slot body contained blacklisted keywords (``axiom`` / ``admit``). Short-circuits grading before the axiom check runs — see ``_aggregate_one_spec``.
    tainted_tokens: list[str] = field(default_factory=list)


@dataclass
class SpecResult:
    module: str
    spec: str
    kinds: list[KindResult]
    status: SpecStatus
    notes: str = ""


@dataclass
class GradeSummary:
    total_specs: int
    passed_specs: int
    unfilled_specs: int
    overfilled_specs: int
    unpaired_sat_specs: int  # sat_<S> filled without a verified joint claim
    failed_specs: int  # sorry_leaked + axiom_leaked + build_error
    joint_passed: bool  # codeproof only; False in proof mode
    joint_status: str | None = None
    joint_specs: list[str] = field(default_factory=list)


def _kinds_for_mode(mode: str) -> list[str]:
    if mode == "proof":
        return ["prove", "disprove"]
    return ["prove", "unsat", "sat"]


def _axiom_index(
    axioms: list[AxiomCheckResult],
) -> dict[str, AxiomCheckResult]:
    return {a.theorem: a for a in axioms}


def grade_specs(
    bench: Benchmark,
    artifact: Artifact,
    axioms: list[AxiomCheckResult],
    *,
    mode: str,
    joint_specs: tuple[str, ...] = (),
    joint_ok: bool = False,
    unsafe_detected: bool = False,
    unsafe_reason: str = "",
    voided_status: SpecStatus | None = None,
    voided_reason: str = "",
) -> tuple[list[SpecResult], GradeSummary]:
    """Grade every spec in the benchmark and build a summary.

    A hygiene pre-pass hit short-circuits the whole run: every spec grades a
    fixed void status regardless of filling / axiom status. ``unsafe_detected``
    (legacy) forces ``unsafe_keyword``; the general ``voided_status`` /
    ``voided_reason`` pair forces any void status (e.g. ``impl_oracle`` when an
    agent impl uses ``@[implemented_by]``). ``unsafe_detected`` takes precedence
    for back-compat when both are supplied.
    """
    # Normalize the two void mechanisms into one.
    if unsafe_detected:
        voided_status = "unsafe_keyword"
        voided_reason = (
            unsafe_reason or "`unsafe` keyword detected in agent-editable file"
        )
    ax_by_name = _axiom_index(axioms)
    proof_slots_by_name = {
        s.def_name: s
        for s in slots_by(artifact, key="proof", prefix="benchmark")
        if s.def_name is not None
    }

    results: list[SpecResult] = []

    for module in bench.iter_modules():
        for spec in module.specs:
            bare = spec.removeprefix("spec_")
            kind_results: list[KindResult] = []
            for kind in _kinds_for_mode(mode):
                thm = f"{kind}_{bare}"
                slot = proof_slots_by_name.get(thm)
                filled = (
                    slot is not None
                    and slot.found
                    and not slot.contains_sorry
                    and not slot.is_empty
                )
                tainted: list[str] = []
                if slot is not None and slot.found:
                    if slot.contains_axiom:
                        tainted.append("axiom")
                    if slot.contains_admit:
                        tainted.append("admit")
                ax = ax_by_name.get(thm)
                ax_status = ax.status if ax else "missing"
                kind_results.append(
                    KindResult(
                        kind=kind,
                        thm_name=thm,
                        filled=filled,
                        axiom_status=ax_status,
                        axioms=list(ax.axioms) if ax else [],
                        tainted_tokens=tainted,
                    )
                )

            if voided_status is not None:
                status: SpecStatus = voided_status
                notes = voided_reason or f"run voided ({voided_status})"
            else:
                # Mode-specific aggregation.
                status, notes = _aggregate_one_spec(
                    kind_results,
                    mode=mode,
                    spec=spec,
                    is_joint=(spec in joint_specs),
                    joint_ok=joint_ok,
                )
            results.append(
                SpecResult(
                    module=module.name,
                    spec=spec,
                    kinds=kind_results,
                    status=status,
                    notes=notes,
                )
            )

    passed = sum(1 for r in results if r.status == "passed")
    unfilled = sum(1 for r in results if r.status == "unfilled")
    overfilled = sum(1 for r in results if r.status == "overfilled")
    unpaired_sat = sum(1 for r in results if r.status == "unpaired_sat")
    failed = sum(
        1
        for r in results
        if r.status
        in {
            "sorry_leaked",
            "axiom_leaked",
            "slot_body_tainted",
            "build_error",
            "unsafe_keyword",
            "impl_oracle",
        }
    )

    summary = GradeSummary(
        total_specs=len(results),
        passed_specs=passed,
        unfilled_specs=unfilled,
        overfilled_specs=overfilled,
        unpaired_sat_specs=unpaired_sat,
        failed_specs=failed,
        joint_passed=joint_ok and mode == "codeproof",
        joint_status=None,
        joint_specs=list(joint_specs),
    )
    return results, summary


def _aggregate_one_spec(
    kinds: list[KindResult],
    *,
    mode: str,
    spec: str,
    is_joint: bool,
    joint_ok: bool,
) -> tuple[SpecStatus, str]:
    """Decide a single spec's status given its per-kind axiom-check results.

    The hygiene checks (tainted / sorry / user-axiom / build_error) apply
    identically in both modes; only the overfill message and the codeproof
    ``sat_<S>`` pairing rule differ.
    """
    filled = [k for k in kinds if k.filled]
    if not filled:
        return "unfilled", ""

    if len(filled) > 1:
        msg = (
            "both prove_* and disprove_* were filled; ambiguous"
            if mode == "proof"
            else "multiple of prove/unsat/sat filled; ambiguous"
        )
        return "overfilled", msg

    tainted = [k for k in filled if k.tainted_tokens]
    if tainted:
        toks = ", ".join(tainted[0].tainted_tokens)
        return (
            "slot_body_tainted",
            f"{tainted[0].thm_name} body contains blacklisted token(s): {toks}",
        )
    for k in filled:
        if k.axiom_status == "uses_sorry":
            return "sorry_leaked", f"{k.thm_name} still depends on sorryAx"
        if k.axiom_status == "uses_user_axiom":
            return "axiom_leaked", f"{k.thm_name} uses user axioms"
        if k.axiom_status in {"build_error", "missing"}:
            return "build_error", f"{k.thm_name} did not compile"

    if mode == "proof":
        return "passed", ""

    # Codeproof: ``prove_<S>`` and ``unsat_<S>`` are claims about the agent's own impl and pass on their own when axiom-clean. ``sat_<S>`` alone is trivially satisfied by any impl, so it only counts when paired with a verified ``joint_unsat`` claim naming ``S`` — then the combination shows individual satisfiability plus joint unsatisfiability with other specs.
    chosen = filled[0]
    if chosen.kind != "sat":
        return "passed", ""
    if not is_joint:
        return (
            "unpaired_sat",
            "sat_<S> is only accepted when paired with a verified "
            "joint_unsat block that names this spec",
        )
    if not joint_ok:
        return (
            "unpaired_sat",
            "sat_<S> is paired with a joint_unsat block but the joint "
            "claim did not verify (rerender failed)",
        )
    return "passed", "sat paired with verified joint_unsat claim"


def _module_lookup(bench: Benchmark, name: str) -> Module | None:
    for m in bench.iter_modules():
        if m.name == name:
            return m
    return None
