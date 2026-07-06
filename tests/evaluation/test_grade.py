"""Grading logic tests (no Lean required)."""

from __future__ import annotations

from pathlib import Path

from vero.evaluation.axioms import AxiomCheckResult
from vero.evaluation.grade import grade_specs
from vero.generation.benchmark import Benchmark
from vero.generation.extractor import (
    Artifact,
    ExtractedSlot,
)

REPO_ROOT = Path(__file__).resolve().parents[2]
REF = REPO_ROOT / "reference" / "BankLedger"


def _slot(
    key: str, def_name: str, body: list[str], prefix: str = "benchmark"
) -> ExtractedSlot:
    from vero.generation.extractor import (
        _contains_admit,
        _contains_axiom,
        _contains_sorry,
        _hash_body,
        _is_effectively_empty,
    )

    return ExtractedSlot(
        file="BankLedger/Proof/Account.lean",
        prefix=prefix,
        key=key,
        def_name=def_name,
        expected_kind=None,
        expected_target=None,
        found=True,
        body_lines=body,
        body_hash=_hash_body(body),
        is_empty=_is_effectively_empty(body),
        contains_sorry=_contains_sorry(body),
        contains_axiom=_contains_axiom(body),
        contains_admit=_contains_admit(body),
        actual_fields={"def": def_name},
        start_line=1,
        end_line=2,
        error="",
    )


def _mk_artifact(slots: list[ExtractedSlot]) -> Artifact:
    return Artifact(
        benchmark_id="bank_ledger_reference",
        mode="proof",
        sandbox_dir="/tmp/fake",
        slots=slots,
    )


def _axiom(thm: str, status: str, axs: list[str] | None = None) -> AxiomCheckResult:
    return AxiomCheckResult(theorem=thm, status=status, axioms=axs or [])


def test_proof_mode_exact_one_filled_passes() -> None:
    bench = Benchmark(REF)
    # For spec_create_zero_balance: prove filled, disprove sorry.
    slots = [
        _slot("proof", "prove_create_zero_balance", ["  decide"]),
        _slot("proof", "disprove_create_zero_balance", ["  sorry"]),
    ]
    axioms = [
        _axiom("prove_create_zero_balance", "clean"),
        _axiom("disprove_create_zero_balance", "uses_sorry"),
    ]
    # Fill all other specs as sorry so unfilled count is most.
    for m in bench.iter_modules():
        for spec in m.specs:
            if spec == "spec_create_zero_balance":
                continue
            bare = spec[len("spec_") :]
            slots.append(_slot("proof", f"prove_{bare}", ["  sorry"]))
            slots.append(_slot("proof", f"disprove_{bare}", ["  sorry"]))
            axioms.append(_axiom(f"prove_{bare}", "uses_sorry"))
            axioms.append(_axiom(f"disprove_{bare}", "uses_sorry"))
    results, summary = grade_specs(bench, _mk_artifact(slots), axioms, mode="proof")
    target = [r for r in results if r.spec == "spec_create_zero_balance"][0]
    assert target.status == "passed"
    assert summary.passed_specs == 1
    assert summary.unfilled_specs == 10


def test_proof_mode_both_filled_is_overfilled() -> None:
    bench = Benchmark(REF)
    slots = []
    axioms = []
    for m in bench.iter_modules():
        for spec in m.specs:
            bare = spec[len("spec_") :]
            if spec == "spec_create_zero_balance":
                slots.append(_slot("proof", f"prove_{bare}", ["  decide"]))
                slots.append(_slot("proof", f"disprove_{bare}", ["  decide"]))
                axioms.append(_axiom(f"prove_{bare}", "clean"))
                axioms.append(_axiom(f"disprove_{bare}", "clean"))
            else:
                slots.append(_slot("proof", f"prove_{bare}", ["  sorry"]))
                slots.append(_slot("proof", f"disprove_{bare}", ["  sorry"]))
                axioms.append(_axiom(f"prove_{bare}", "uses_sorry"))
                axioms.append(_axiom(f"disprove_{bare}", "uses_sorry"))
    results, summary = grade_specs(bench, _mk_artifact(slots), axioms, mode="proof")
    target = [r for r in results if r.spec == "spec_create_zero_balance"][0]
    assert target.status == "overfilled"
    assert summary.overfilled_specs == 1


def test_codeproof_sat_without_joint_is_unpaired_sat() -> None:
    """sat alone is rejected — it's trivially satisfiable by ad-hoc impls."""
    bench = Benchmark(REF)
    slots = []
    axioms = []
    for m in bench.iter_modules():
        for spec in m.specs:
            bare = spec[len("spec_") :]
            if spec == "spec_create_zero_balance":
                slots.append(_slot("proof", f"prove_{bare}", ["  sorry"]))
                slots.append(_slot("proof", f"unsat_{bare}", ["  sorry"]))
                slots.append(_slot("proof", f"sat_{bare}", ["  decide"]))
                axioms.append(_axiom(f"prove_{bare}", "uses_sorry"))
                axioms.append(_axiom(f"unsat_{bare}", "uses_sorry"))
                axioms.append(_axiom(f"sat_{bare}", "clean"))
            else:
                for k in ("prove", "unsat", "sat"):
                    slots.append(_slot("proof", f"{k}_{bare}", ["  sorry"]))
                    axioms.append(_axiom(f"{k}_{bare}", "uses_sorry"))
    results, summary = grade_specs(
        bench,
        _mk_artifact(slots),
        axioms,
        mode="codeproof",
        joint_specs=(),
        joint_ok=False,
    )
    target = [r for r in results if r.spec == "spec_create_zero_balance"][0]
    assert target.status == "unpaired_sat"
    assert summary.unpaired_sat_specs == 1
    assert summary.passed_specs == 0


def test_codeproof_sat_with_joint_ok_passes() -> None:
    bench = Benchmark(REF)
    slots = []
    axioms = []
    for m in bench.iter_modules():
        for spec in m.specs:
            bare = spec[len("spec_") :]
            if spec in {"spec_create_zero_balance", "spec_create_exists"}:
                slots.append(_slot("proof", f"prove_{bare}", ["  sorry"]))
                slots.append(_slot("proof", f"unsat_{bare}", ["  sorry"]))
                slots.append(_slot("proof", f"sat_{bare}", ["  decide"]))
                axioms.append(_axiom(f"prove_{bare}", "uses_sorry"))
                axioms.append(_axiom(f"unsat_{bare}", "uses_sorry"))
                axioms.append(_axiom(f"sat_{bare}", "clean"))
            else:
                for k in ("prove", "unsat", "sat"):
                    slots.append(_slot("proof", f"{k}_{bare}", ["  sorry"]))
                    axioms.append(_axiom(f"{k}_{bare}", "uses_sorry"))
    results, summary = grade_specs(
        bench,
        _mk_artifact(slots),
        axioms,
        mode="codeproof",
        joint_specs=("spec_create_zero_balance", "spec_create_exists"),
        joint_ok=True,
    )
    targets = [r for r in results if r.spec.startswith("spec_create_")]
    assert all(t.status == "passed" for t in targets)
    assert summary.joint_passed


# ─── Syntactic slot-body taint ─────────────────────────────────


def _mk_single_filled_artifact(
    bench: Benchmark, mode: str, target_spec: str, filled_kind: str, body: list[str]
) -> Artifact:
    """Build a minimal artifact where exactly `target_spec`'s `filled_kind` has `body`; everything else is sorry."""
    kinds = ("prove", "disprove") if mode == "proof" else ("prove", "unsat", "sat")
    slots: list[ExtractedSlot] = []
    for m in bench.iter_modules():
        for spec in m.specs:
            bare = spec[len("spec_") :]
            for k in kinds:
                if spec == target_spec and k == filled_kind:
                    slots.append(_slot("proof", f"{k}_{bare}", body))
                else:
                    slots.append(_slot("proof", f"{k}_{bare}", ["  sorry"]))
    return Artifact(
        benchmark_id="bank_ledger_reference",
        mode=mode,
        sandbox_dir="/tmp/fake",
        slots=slots,
    )


def test_slot_body_tainted_by_axiom_keyword() -> None:
    """A filled proof body containing `axiom` gets rejected before axiom check."""
    bench = Benchmark(REF)
    artifact = _mk_single_filled_artifact(
        bench,
        "proof",
        "spec_create_zero_balance",
        "prove",
        ["  axiom bogus : False", "  exact bogus.elim"],
    )
    # Axiom-check reports "clean" to demonstrate taint short-circuits ahead.
    axioms = []
    for m in bench.iter_modules():
        for spec in m.specs:
            bare = spec[len("spec_") :]
            for k in ("prove", "disprove"):
                axioms.append(
                    _axiom(
                        f"{k}_{bare}",
                        "clean" if spec == "spec_create_zero_balance" else "uses_sorry",
                    )
                )
    results, summary = grade_specs(bench, artifact, axioms, mode="proof")
    target = [r for r in results if r.spec == "spec_create_zero_balance"][0]
    assert target.status == "slot_body_tainted"
    assert "axiom" in target.notes
    assert summary.passed_specs == 0
    assert summary.failed_specs == 1


def test_slot_body_tainted_by_admit_keyword() -> None:
    bench = Benchmark(REF)
    artifact = _mk_single_filled_artifact(
        bench, "proof", "spec_create_zero_balance", "prove", ["  admit"]
    )
    axioms = []
    for m in bench.iter_modules():
        for spec in m.specs:
            bare = spec[len("spec_") :]
            for k in ("prove", "disprove"):
                axioms.append(_axiom(f"{k}_{bare}", "uses_sorry"))
    results, _ = grade_specs(bench, artifact, axioms, mode="proof")
    target = [r for r in results if r.spec == "spec_create_zero_balance"][0]
    assert target.status == "slot_body_tainted"
    assert "admit" in target.notes


def test_keyword_check_whole_word_only() -> None:
    """`sorryAx`, `Axiom.Foo`, `admitRight` do NOT count as tainted — whole-word match."""
    from vero.generation.extractor import (
        _contains_admit,
        _contains_axiom,
        _contains_sorry,
    )

    # Not tainted — non-word continuation of the keyword
    assert not _contains_sorry(["  exact sorryAx"])
    assert not _contains_axiom(["  import Foo.Axiom"])
    assert not _contains_admit(["  admitRight trivial"])
    # Tainted — word-boundary match
    assert _contains_sorry(["  sorry"])
    assert _contains_axiom(["  axiom foo : False"])
    assert _contains_admit(["  admit"])
    # Line comments are stripped
    assert not _contains_axiom(["  -- axiom foo : False"])
    # Block comments too
    assert not _contains_axiom(["/- axiom foo : False -/", "  decide"])
