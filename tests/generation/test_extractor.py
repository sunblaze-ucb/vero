"""Tests for ``vero.generation.extractor`` (schema-driven)."""

from __future__ import annotations

from pathlib import Path

import pytest

from vero.generation.benchmark import Benchmark
from vero.generation.extractor import (
    artifact_to_json,
    expected_slots,
    extract,
    proof_slot,
    slots_by,
    solution_slot,
)
from vero.generation.sandbox import create_sandbox

REPO_ROOT = Path(__file__).resolve().parents[2]
REF = REPO_ROOT / "reference" / "BankLedger"


@pytest.fixture()
def proof_sandbox(tmp_path: Path) -> Path:
    out = tmp_path / "sb_proof"
    create_sandbox(REF, out, mode="proof")
    return out


@pytest.fixture()
def codeproof_sandbox(tmp_path: Path) -> Path:
    out = tmp_path / "sb_cp"
    create_sandbox(REF, out, mode="codeproof")
    return out


# ─── expected_slots schedule ────────────────────────────────────


def test_expected_slots_proof_mode_counts() -> None:
    bench = Benchmark(REF)
    sched = expected_slots(bench, mode="proof")
    # Impl: 4 modules × (imports + global_aux) + 10 APIs × (code_aux + code) = 28
    # Proof: 4 modules × (imports + global_aux) + 11 specs × 2 kinds × (proof_aux + proof) = 52
    assert len(sched) == 28 + 52
    counts = {
        k: sum(1 for e in sched if e.key == k)
        for k in {"imports", "global_aux", "code", "code_aux", "proof", "proof_aux"}
    }
    assert counts == {
        "imports": 8,
        "global_aux": 8,  # 4 impl + 4 proof files
        "code": 10,
        "code_aux": 10,
        "proof": 22,
        "proof_aux": 22,
    }


def test_expected_slots_codeproof_mode_counts() -> None:
    bench = Benchmark(REF)
    sched = expected_slots(bench, mode="codeproof")
    # Impl: 28
    # Proof: 4 × 2 + 11 × 3 × 2 = 74
    # Joint: imports + global_aux + solution + proof_aux + claim + proof = 6
    assert len(sched) == 28 + 74 + 6
    # Joint slots with kind=joint_unsat:
    joint_slots = [e for e in sched if e.expected_kind == "joint_unsat"]
    assert len(joint_slots) == 3  # solution + claim + proof


def test_expected_slots_carries_kind_and_target() -> None:
    bench = Benchmark(REF)
    sched = expected_slots(bench, mode="proof")
    prove_slot = next(
        e
        for e in sched
        if e.key == "proof" and e.def_name == "prove_create_zero_balance"
    )
    assert prove_slot.expected_kind == "prove"
    assert prove_slot.expected_target == "spec_create_zero_balance"
    disprove_slot = next(
        e
        for e in sched
        if e.key == "proof" and e.def_name == "disprove_create_zero_balance"
    )
    assert disprove_slot.expected_kind == "disprove"


# ─── extract against the schedule ───────────────────────────────


def test_extract_proof_mode_returns_exactly_expected(proof_sandbox: Path) -> None:
    bench = Benchmark(REF)
    a = extract(proof_sandbox, bench, mode="proof")
    assert a.benchmark_id == "bank_ledger_reference"
    assert a.mode == "proof"
    assert len(a.slots) == len(expected_slots(bench, mode="proof"))
    # Every expected slot found on a fresh sandbox.
    assert all(s.found for s in a.slots), [s for s in a.slots if not s.found][:3]
    # No extras, no file errors.
    assert a.extras == []
    assert a.file_errors == {}
    # All proof slots are sorry stubs right after materialize.
    proof_ss = slots_by(a, key="proof")
    assert len(proof_ss) == 22
    assert all(s.contains_sorry for s in proof_ss)


def test_extract_codeproof_mode_counts(codeproof_sandbox: Path) -> None:
    a = extract(codeproof_sandbox, Benchmark(REF), mode="codeproof")
    proof_ss = slots_by(a, key="proof")
    assert len(proof_ss) == 34  # 33 per-spec + 1 joint
    # Joint slot present + found
    joint = proof_slot(a, "joint_unsatisfiability")
    assert joint is not None and joint.found
    sol = solution_slot(a, "joint_unsatisfiability")
    assert sol is not None and sol.found


def test_extract_missing_slot_when_agent_deletes_marker(proof_sandbox: Path) -> None:
    """If the agent deletes a marker, the expected slot is reported as missing."""
    # Pick a proof slot and delete its marker lines + body.
    target = proof_sandbox / "BankLedger/Proof/Account.lean"
    text = target.read_text()
    # Remove the prove_create_zero_balance block (start, body, end) wholesale.
    start_marker = (
        "-- !benchmark @start proof def=prove_create_zero_balance "
        "kind=prove target=spec_create_zero_balance"
    )
    end_marker = "-- !benchmark @end proof def=prove_create_zero_balance"
    assert start_marker in text and end_marker in text
    start = text.index(start_marker)
    end = text.index(end_marker) + len(end_marker)
    target.write_text(text[:start] + text[end + 1 :])

    a = extract(proof_sandbox, Benchmark(REF), mode="proof")
    slot = proof_slot(a, "prove_create_zero_balance")
    assert slot is not None
    assert slot.found is False
    assert slot.error == "missing"
    # Partner slot (disprove) should still be found.
    other = proof_slot(a, "disprove_create_zero_balance")
    assert other is not None and other.found


def test_extract_flags_extra_slot(proof_sandbox: Path) -> None:
    """An agent-added marker not in the schedule lands in ``extras``."""
    target = proof_sandbox / "BankLedger/Proof/Account.lean"
    text = target.read_text()
    inject = (
        "\n-- !benchmark @start proof def=bogus_theorem kind=prove target=spec_create_zero_balance\n"
        "  trivial\n"
        "-- !benchmark @end proof def=bogus_theorem\n"
    )
    target.write_text(text + inject)
    a = extract(proof_sandbox, Benchmark(REF), mode="proof")
    assert any(x.def_name == "bogus_theorem" for x in a.extras)


def test_extract_codeproof_blank_impl_code_slots(codeproof_sandbox: Path) -> None:
    a = extract(codeproof_sandbox, Benchmark(REF), mode="codeproof")
    code_slots = slots_by(a, key="code")
    assert len(code_slots) == 10
    for s in code_slots:
        assert s.contains_sorry, f"{s.def_name} should contain sorry"


def test_extract_proof_mode_keeps_impl_bodies(proof_sandbox: Path) -> None:
    a = extract(proof_sandbox, Benchmark(REF), mode="proof")
    code_slots = slots_by(a, key="code")
    assert len(code_slots) == 10
    non_sorry = [s for s in code_slots if not s.contains_sorry]
    assert len(non_sorry) == 10


def test_artifact_json_round_trip(proof_sandbox: Path) -> None:
    a = extract(proof_sandbox, Benchmark(REF), mode="proof")
    text = artifact_to_json(a)
    assert "bank_ledger_reference" in text
    assert '"key": "proof"' in text
    assert '"extras"' in text
    assert '"file_errors"' in text
