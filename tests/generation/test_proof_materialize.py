"""End-to-end test: materializing Proof/ against reference/BankLedger/ must

produce per-module files whose structure matches the hand-crafted
illustrations at Proof_modeproof/ and Proof_modecodeproof/.
"""

from __future__ import annotations

import json
import shutil
from pathlib import Path

import pytest

from vero.curation.validation.markers import parse_file_markers
from vero.generation.proof_materialize import materialize_proof

REPO_ROOT = Path(__file__).parent.parent.parent
REFERENCE_BANKLEDGER = REPO_ROOT / "reference" / "BankLedger"


def _copy_bankledger_to_tmp(tmp_path: Path) -> Path:
    """Snapshot the reference tree so tests can write Proof/ without dirtying the repo.

    Skip ``.lake/`` (Lake's package + build cache, multi-GB once mathlib
    is fetched) and other build artefacts — they aren't part of the
    benchmark contract and would dominate per-test wall-time. Mirrors
    the production ``_copy_benchmark`` ignore set in
    ``src/vero/generation/sandbox.py``.
    """
    dst = tmp_path / "BankLedger"
    shutil.copytree(
        REFERENCE_BANKLEDGER,
        dst,
        ignore=shutil.ignore_patterns(".lake", "build", ".git", "__pycache__"),
    )
    # Remove any existing Proof/ or illustration dirs so materialize starts clean.
    for p in (
        dst / "BankLedger" / "Proof",
        dst / "BankLedger" / "Proof_modeproof",
        dst / "BankLedger" / "Proof_modecodeproof",
    ):
        if p.exists():
            shutil.rmtree(p)
    return dst


# ─── proof mode ─────────────────────────────────────────────


def test_materialize_proof_mode(tmp_path: Path) -> None:
    benchmark = _copy_bankledger_to_tmp(tmp_path)
    result = materialize_proof(benchmark, mode="proof")
    assert result.mode == "proof"
    assert len(result.files_written) == 4  # 4 modules in BankLedger
    for p in result.files_written:
        assert p.exists()
        assert p.parent.name == "Proof"
        assert p.suffix == ".lean"

    # Account has 4 specs × 2 stubs (prove + disprove) = 8 theorems.
    account = benchmark / "BankLedger" / "Proof" / "Account.lean"
    text = account.read_text()
    assert text.count("theorem prove_") == 4
    assert text.count("theorem disprove_") == 4
    assert "¬ spec_create_zero_balance canonical" in text
    assert "canonical := by" in text
    assert "sorry" in text


def test_materialize_accepts_rich_spec_entries(tmp_path: Path) -> None:
    """Rich curation spec entries materialize to proof stubs by declaration name."""
    benchmark = tmp_path / "RichSpecs"
    benchmark.mkdir()
    (benchmark / "manifest.json").write_text(
        json.dumps(
            {
                "benchmark_id": "rich_specs",
                "lean_version": "4.22.0",
                "modes_supported": ["proof"],
                "root_package": "RichSpecs",
                "packages": [
                    {
                        "name": "RichSpecs",
                        "bundle": "RichSpecs/Bundle.lean",
                        "bundle_type": "RichSpecsBundle",
                        "repo_impl_field": "richSpecs",
                        "modules": [
                            {
                                "name": "Utils/Seq",
                                "spec": "RichSpecs/Spec/Utils/Seq.lean",
                                "specs": [
                                    {"name": "spec_from_dict"},
                                    "spec_from_string",
                                ],
                            }
                        ],
                    }
                ],
            }
        )
    )

    materialize_proof(benchmark, mode="proof")

    proof = benchmark / "RichSpecs" / "Proof" / "Utils" / "Seq.lean"
    text = proof.read_text()
    assert "import RichSpecs.Spec.Utils.Seq" in text
    assert "theorem prove_from_dict : spec_from_dict canonical := by" in text
    assert "theorem disprove_from_string : ¬ spec_from_string canonical := by" in text


def test_materialize_proof_mode_markers(tmp_path: Path) -> None:
    benchmark = _copy_bankledger_to_tmp(tmp_path)
    materialize_proof(benchmark, mode="proof")
    account = benchmark / "BankLedger" / "Proof" / "Account.lean"
    markers = parse_file_markers(account)
    keys = [m.key for m in markers if m.prefix == "benchmark"]
    # imports + global_aux (2×2 = 4 lines) + (proof_aux + proof) × 8 stubs = 32 lines
    assert keys.count("imports") == 2
    assert keys.count("global_aux") == 2
    assert keys.count("proof_aux") == 16  # 8 stubs × (start + end)
    assert keys.count("proof") == 16
    # Kind values for proof markers (on @start only)
    start_kinds = [
        m.fields.get("kind")
        for m in markers
        if m.prefix == "benchmark" and m.key == "proof" and m.boundary == "start"
    ]
    assert sorted(start_kinds) == ["disprove"] * 4 + ["prove"] * 4


def test_materialize_proof_mode_no_joint(tmp_path: Path) -> None:
    benchmark = _copy_bankledger_to_tmp(tmp_path)
    materialize_proof(benchmark, mode="proof")
    assert not (benchmark / "BankLedger" / "Proof" / "Joint.lean").exists()


# ─── codeproof mode ──────────────────────────────────────────


def test_materialize_codeproof_mode(tmp_path: Path) -> None:
    benchmark = _copy_bankledger_to_tmp(tmp_path)
    result = materialize_proof(benchmark, mode="codeproof")
    assert result.mode == "codeproof"
    # 4 module files + 1 Joint.lean
    assert len(result.files_written) == 5

    account = benchmark / "BankLedger" / "Proof" / "Account.lean"
    text = account.read_text()
    # Per spec: prove + unsat + sat = 3 theorems. 4 specs → 12.
    assert text.count("theorem prove_") == 4
    assert text.count("theorem unsat_") == 4
    assert text.count("theorem sat_") == 4
    assert "¬ ∃ impl : RepoImpl" in text
    assert "∃ impl : RepoImpl, spec_" in text


def test_materialize_codeproof_joint(tmp_path: Path) -> None:
    benchmark = _copy_bankledger_to_tmp(tmp_path)
    materialize_proof(benchmark, mode="codeproof")
    joint = benchmark / "BankLedger" / "Proof" / "Joint.lean"
    assert joint.exists()
    text = joint.read_text()
    # Must have !solution + !benchmark claim + !benchmark proof blocks, all commented.
    assert "-- !solution @start def=joint_unsatisfiability kind=joint_unsat" in text
    assert "-- !solution @end def=joint_unsatisfiability" in text
    assert "-- joint_unsat <specs> by" in text  # commented macro-call template
    assert "-- sorry" in text  # commented proof body


def test_materialize_codeproof_joint_markers(tmp_path: Path) -> None:
    benchmark = _copy_bankledger_to_tmp(tmp_path)
    materialize_proof(benchmark, mode="codeproof")
    joint = benchmark / "BankLedger" / "Proof" / "Joint.lean"
    markers = parse_file_markers(joint)
    solution_markers = [m for m in markers if m.prefix == "solution"]
    assert len(solution_markers) == 2  # one @start, one @end
    assert solution_markers[0].boundary == "start"
    assert solution_markers[0].fields == {
        "def": "joint_unsatisfiability",
        "kind": "joint_unsat",
    }

    benchmark_markers = [m for m in markers if m.prefix == "benchmark"]
    keys = [m.key for m in benchmark_markers]
    # imports + global_aux + proof_aux + claim + proof = 5 pairs = 10 lines
    assert keys.count("imports") == 2
    assert keys.count("global_aux") == 2
    assert keys.count("proof_aux") == 2
    assert keys.count("claim") == 2
    assert keys.count("proof") == 2


# ─── shape invariant: materialized output validates ─────────


@pytest.mark.parametrize("mode", ["proof", "codeproof"])
def test_materialized_tree_passes_validation(tmp_path: Path, mode: str) -> None:
    """End-to-end: materialized Proof/ + untouched Impl/Spec/Harness should
    pass every rule-based check except the slow `lake build`."""
    from vero.curation.validation import validate_benchmark

    benchmark = _copy_bankledger_to_tmp(tmp_path)
    materialize_proof(benchmark, mode=mode)
    report = validate_benchmark(benchmark, skip_build=True)
    assert report.overall in {"pass", "warn"}, (
        f"materialized {mode} tree failed validation:\n"
        f"blockers: {report.blockers}\n"
        f"rule_checks: { {k: v.status for k, v in report.rule_checks.items()} }"
    )
    assert not report.blockers, report.blockers


@pytest.mark.parametrize("mode", ["proof", "codeproof"])
def test_dry_run_writes_nothing(tmp_path: Path, mode: str) -> None:
    benchmark = _copy_bankledger_to_tmp(tmp_path)
    result = materialize_proof(benchmark, mode=mode, dry_run=True)
    for p in result.files_written:
        assert not p.exists(), f"dry_run wrote {p}"
