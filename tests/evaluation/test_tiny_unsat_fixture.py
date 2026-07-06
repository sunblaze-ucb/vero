"""End-to-end eval test on `tests/fixtures/tiny_unsat/`.

Exercises codeproof-mode paths that real agent runs haven't touched yet:

- `unsat_<S>` — agent proves a spec is unsatisfiable by any impl.
- Joint-unsat rerender — agent claims ≥ 2 specs are jointly
  unsatisfiable and the grader re-renders the macro from the
  ``!solution`` list + ``!benchmark proof`` body and compiles it.

The fixture has three specs:

- ``spec_impossible``       — ``answer = answer + 1``, individually unsat.
- ``spec_answer_is_one``    — ``answer = 1``, individually sat.
- ``spec_answer_is_two``    — ``answer = 2``, individually sat.

Jointly (answer_is_one ∧ answer_is_two) is unsatisfiable.

No agent runs here — we materialize the sandbox, overwrite the
relevant files with pre-baked proof content, extract the artifact,
and run the evaluator.
"""

from __future__ import annotations

from pathlib import Path

import pytest

from vero.evaluation.runner import run_evaluation
from vero.generation.benchmark import Benchmark
from vero.generation.extractor import extract
from vero.generation.sandbox import create_sandbox

REPO_ROOT = Path(__file__).resolve().parents[2]
FIXTURE = REPO_ROOT / "tests" / "fixtures" / "tiny_unsat"


# ─── Pre-baked fillings ────────────────────────────────────────


_IMPL_CORE = """\
-- !benchmark @start imports
-- !benchmark @end imports

/-!
# TinyUnsat.Impl.Core
-/

namespace TU

abbrev AnswerSig := Nat

end TU

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- !benchmark @start code_aux def=answer
-- !benchmark @end code_aux def=answer

def TU.answer : TU.AnswerSig :=
-- !benchmark @start code def=answer
  1
-- !benchmark @end code def=answer
"""


# The Proof/Core.lean layout is emitted by ``materialize_proof``; we
# overwrite it in full. Filled slots:
#   - unsat_impossible        (proves the spec is unsat by any impl)
#   - sat_answer_is_one       (paired with joint)
#   - sat_answer_is_two       (paired with joint)
# Everything else stays sorry.
_PROOF_CORE = """\
import TinyUnsat.Harness
import TinyUnsat.Spec.Core

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# TinyUnsat.Proof.Core — hand-filled for eval fixture.
-/

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- ── spec_impossible ──
-- !benchmark @start proof_aux def=prove_impossible
-- !benchmark @end proof_aux def=prove_impossible

theorem prove_impossible : spec_impossible canonical := by
-- !benchmark @start proof def=prove_impossible kind=prove target=spec_impossible
  sorry
-- !benchmark @end proof def=prove_impossible

-- !benchmark @start proof_aux def=unsat_impossible
-- !benchmark @end proof_aux def=unsat_impossible

theorem unsat_impossible : ¬ ∃ impl : RepoImpl, spec_impossible impl := by
-- !benchmark @start proof def=unsat_impossible kind=unsat target=spec_impossible
  rintro ⟨impl, h⟩
  simp [spec_impossible] at h
-- !benchmark @end proof def=unsat_impossible

-- !benchmark @start proof_aux def=sat_impossible
-- !benchmark @end proof_aux def=sat_impossible

theorem sat_impossible : ∃ impl : RepoImpl, spec_impossible impl := by
-- !benchmark @start proof def=sat_impossible kind=sat target=spec_impossible
  sorry
-- !benchmark @end proof def=sat_impossible

-- ── spec_answer_is_one ──
-- !benchmark @start proof_aux def=prove_answer_is_one
-- !benchmark @end proof_aux def=prove_answer_is_one

theorem prove_answer_is_one : spec_answer_is_one canonical := by
-- !benchmark @start proof def=prove_answer_is_one kind=prove target=spec_answer_is_one
  sorry
-- !benchmark @end proof def=prove_answer_is_one

-- !benchmark @start proof_aux def=unsat_answer_is_one
-- !benchmark @end proof_aux def=unsat_answer_is_one

theorem unsat_answer_is_one : ¬ ∃ impl : RepoImpl, spec_answer_is_one impl := by
-- !benchmark @start proof def=unsat_answer_is_one kind=unsat target=spec_answer_is_one
  sorry
-- !benchmark @end proof def=unsat_answer_is_one

-- !benchmark @start proof_aux def=sat_answer_is_one
-- !benchmark @end proof_aux def=sat_answer_is_one

theorem sat_answer_is_one : ∃ impl : RepoImpl, spec_answer_is_one impl := by
-- !benchmark @start proof def=sat_answer_is_one kind=sat target=spec_answer_is_one
  exact ⟨{ tiny := { answer := 1 } }, rfl⟩
-- !benchmark @end proof def=sat_answer_is_one

-- ── spec_answer_is_two ──
-- !benchmark @start proof_aux def=prove_answer_is_two
-- !benchmark @end proof_aux def=prove_answer_is_two

theorem prove_answer_is_two : spec_answer_is_two canonical := by
-- !benchmark @start proof def=prove_answer_is_two kind=prove target=spec_answer_is_two
  sorry
-- !benchmark @end proof def=prove_answer_is_two

-- !benchmark @start proof_aux def=unsat_answer_is_two
-- !benchmark @end proof_aux def=unsat_answer_is_two

theorem unsat_answer_is_two : ¬ ∃ impl : RepoImpl, spec_answer_is_two impl := by
-- !benchmark @start proof def=unsat_answer_is_two kind=unsat target=spec_answer_is_two
  sorry
-- !benchmark @end proof def=unsat_answer_is_two

-- !benchmark @start proof_aux def=sat_answer_is_two
-- !benchmark @end proof_aux def=sat_answer_is_two

theorem sat_answer_is_two : ∃ impl : RepoImpl, spec_answer_is_two impl := by
-- !benchmark @start proof def=sat_answer_is_two kind=sat target=spec_answer_is_two
  exact ⟨{ tiny := { answer := 2 } }, rfl⟩
-- !benchmark @end proof def=sat_answer_is_two
"""


_PROOF_JOINT = """\
import TinyUnsat.Harness
import TinyUnsat.Spec.Core

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# TinyUnsat.Proof.Joint — hand-filled for eval fixture.
-/

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- !solution @start def=joint_unsatisfiability kind=joint_unsat
-- specs=[spec_answer_is_one, spec_answer_is_two]
-- !solution @end def=joint_unsatisfiability kind=joint_unsat

-- !benchmark @start proof_aux def=joint_unsatisfiability
-- !benchmark @end proof_aux def=joint_unsatisfiability

-- !benchmark @start claim def=joint_unsatisfiability kind=joint_unsat
joint_unsat spec_answer_is_one spec_answer_is_two by
-- !benchmark @end claim def=joint_unsatisfiability

-- !benchmark @start proof def=joint_unsatisfiability kind=joint_unsat
  rintro ⟨impl, h1, h2⟩
  have : (1 : Nat) = 2 := h1.symm.trans h2
  contradiction
-- !benchmark @end proof def=joint_unsatisfiability
"""


# ─── Tests ─────────────────────────────────────────────────────


@pytest.fixture()
def filled_sandbox(tmp_path: Path) -> Path:
    """A codeproof sandbox with hand-filled proofs for the fixture."""
    sandbox = tmp_path / "sandbox"
    create_sandbox(FIXTURE, sandbox, mode="codeproof")
    (sandbox / "TinyUnsat" / "Impl" / "Core.lean").write_text(_IMPL_CORE)
    (sandbox / "TinyUnsat" / "Proof" / "Core.lean").write_text(_PROOF_CORE)
    (sandbox / "TinyUnsat" / "Proof" / "Joint.lean").write_text(_PROOF_JOINT)
    return sandbox


def _requires_lake() -> None:
    """Skip gracefully if `lake` isn't on PATH (CI sans Lean)."""
    import shutil

    if shutil.which("lake") is None:
        pytest.skip("lake not on PATH; skipping Lean-dependent eval test")


def test_eval_passes_unsat_and_joint(filled_sandbox: Path, tmp_path: Path) -> None:
    _requires_lake()

    artifact = extract(filled_sandbox, Benchmark(FIXTURE), mode="codeproof")
    assert len(artifact.extras) == 0, artifact.extras
    assert artifact.file_errors == {}, artifact.file_errors

    eval_sandbox = tmp_path / "eval_sandbox"
    report_dir = tmp_path / "report"
    result = run_evaluation(
        benchmark_dir=FIXTURE,
        artifact=artifact,
        mode="codeproof",
        eval_sandbox_dir=eval_sandbox,
        report_dir=report_dir,
        lake_timeout=300,
    )
    report = result.report

    # Build should succeed — all three filled proofs compile.
    assert report.build_ok, f"lake build failed: {report.build_tail[-400:]}"

    # Joint rerender must have found + verified the claim.
    assert report.joint is not None
    assert report.joint.status == "ok", (
        f"joint status={report.joint.status!r} notes={report.joint.notes!r}"
    )
    assert set(report.joint.specs) == {"spec_answer_is_one", "spec_answer_is_two"}

    statuses = {r.spec: r.status for r in report.specs}
    assert statuses["spec_impossible"] == "passed", statuses
    assert statuses["spec_answer_is_one"] == "passed", statuses
    assert statuses["spec_answer_is_two"] == "passed", statuses

    # Impossible passed via unsat; is_one/is_two passed via sat (paired).
    kinds = {r.spec: [k.kind for k in r.kinds if k.filled] for r in report.specs}
    assert kinds["spec_impossible"] == ["unsat"]
    assert kinds["spec_answer_is_one"] == ["sat"]
    assert kinds["spec_answer_is_two"] == ["sat"]

    # Summary counters
    assert report.summary.passed_specs == 3
    assert report.summary.unpaired_sat_specs == 0
    assert report.summary.joint_passed is True


def test_eval_rejects_joint_with_wrong_specs(tmp_path: Path) -> None:
    """If the !solution block lists a spec that the agent didn't `sat_`-fill,
    the joint claim can still verify (the rerender only cares about the spec
    names + proof body), but per-spec grading is independent.

    Here we replace the !solution list with duplicates to exercise the
    ``duplicate`` branch of joint_rerender.
    """
    _requires_lake()

    sandbox = tmp_path / "sandbox"
    create_sandbox(FIXTURE, sandbox, mode="codeproof")
    (sandbox / "TinyUnsat" / "Impl" / "Core.lean").write_text(_IMPL_CORE)
    (sandbox / "TinyUnsat" / "Proof" / "Core.lean").write_text(_PROOF_CORE)

    joint_with_dupes = _PROOF_JOINT.replace(
        "-- specs=[spec_answer_is_one, spec_answer_is_two]",
        "-- specs=[spec_answer_is_one, spec_answer_is_one]",
    )
    (sandbox / "TinyUnsat" / "Proof" / "Joint.lean").write_text(joint_with_dupes)

    artifact = extract(sandbox, Benchmark(FIXTURE), mode="codeproof")
    result = run_evaluation(
        benchmark_dir=FIXTURE,
        artifact=artifact,
        mode="codeproof",
        eval_sandbox_dir=tmp_path / "eval_sandbox",
        report_dir=tmp_path / "report",
        lake_timeout=300,
    )
    assert result.report.joint is not None
    assert result.report.joint.status == "duplicate"


def test_eval_rejects_sat_without_joint(tmp_path: Path) -> None:
    """With joint.status=no_claim, paired sat_* becomes unpaired_sat."""
    _requires_lake()

    sandbox = tmp_path / "sandbox"
    create_sandbox(FIXTURE, sandbox, mode="codeproof")
    (sandbox / "TinyUnsat" / "Impl" / "Core.lean").write_text(_IMPL_CORE)
    (sandbox / "TinyUnsat" / "Proof" / "Core.lean").write_text(_PROOF_CORE)
    # Leave Joint.lean at the materialize-time default (commented placeholder).

    artifact = extract(sandbox, Benchmark(FIXTURE), mode="codeproof")
    result = run_evaluation(
        benchmark_dir=FIXTURE,
        artifact=artifact,
        mode="codeproof",
        eval_sandbox_dir=tmp_path / "eval_sandbox",
        report_dir=tmp_path / "report",
        lake_timeout=300,
    )
    report = result.report
    assert report.joint is not None
    assert report.joint.status == "no_claim"

    statuses = {r.spec: r.status for r in report.specs}
    # impossible still passes via unsat (no joint needed).
    assert statuses["spec_impossible"] == "passed"
    # The two sat_* claims are now unpaired.
    assert statuses["spec_answer_is_one"] == "unpaired_sat"
    assert statuses["spec_answer_is_two"] == "unpaired_sat"

    assert report.summary.passed_specs == 1
    assert report.summary.unpaired_sat_specs == 2
