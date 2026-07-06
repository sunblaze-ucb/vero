"""Hygiene pre-pass tests — scan agent-editable files for the ``unsafe`` keyword.

Mirrors the whole-word + comment-stripping policy used by the existing
``user_axiom`` / ``slot_body_tainted`` checks (see
``vero.generation.extractor._contains_keyword`` tests in
``tests/evaluation/test_grade.py``). A literal ``unsafe`` in a prose
comment is NOT a cheat; an ``unsafe def`` in code is.
"""

from __future__ import annotations

from pathlib import Path

from vero.evaluation.grade import grade_specs
from vero.evaluation.hygiene import check_unsafe_keyword
from vero.generation.benchmark import Benchmark
from vero.generation.extractor import Artifact, ExtractedSlot

REPO_ROOT = Path(__file__).resolve().parents[2]
REF = REPO_ROOT / "reference" / "BankLedger"


def _write(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def test_unsafe_def_triggers(tmp_path: Path) -> None:
    """Whole-word ``unsafe`` in real code triggers."""
    rel = "A/Impl/Mod.lean"
    _write(tmp_path / rel, "import Lean\n\nunsafe def foo := 42\n")
    res = check_unsafe_keyword(tmp_path, [rel])
    assert res.detected
    assert res.files == [rel]
    assert "unsafe" in res.reason.lower()


def test_clean_file_does_not_trigger(tmp_path: Path) -> None:
    rel = "A/Impl/Clean.lean"
    _write(tmp_path / rel, "def foo := 42\n")
    res = check_unsafe_keyword(tmp_path, [rel])
    assert not res.detected
    assert res.files == []


def test_unsafe_in_line_comment_does_not_trigger(tmp_path: Path) -> None:
    rel = "A/Impl/CommentOK.lean"
    _write(tmp_path / rel, "-- this would be unsafe if we used it\ndef foo := 42\n")
    res = check_unsafe_keyword(tmp_path, [rel])
    assert not res.detected


def test_unsafe_in_block_comment_does_not_trigger(tmp_path: Path) -> None:
    rel = "A/Impl/BlockCommentOK.lean"
    _write(
        tmp_path / rel, "/- discussion of unsafe keyword semantics -/\ndef foo := 42\n"
    )
    res = check_unsafe_keyword(tmp_path, [rel])
    assert not res.detected


def test_unsafe_substring_word_does_not_trigger(tmp_path: Path) -> None:
    """``unsafely`` / ``unsafePerformIO`` etc. should not count (whole-word only)."""
    rel = "A/Impl/Sub.lean"
    _write(tmp_path / rel, "def unsafelyNamed := 42\ndef unsafePerformFoo := 1\n")
    res = check_unsafe_keyword(tmp_path, [rel])
    assert not res.detected


def test_multiple_files_all_reported(tmp_path: Path) -> None:
    _write(tmp_path / "A/Impl/One.lean", "unsafe def a := 1\n")
    _write(tmp_path / "A/Impl/Two.lean", "unsafe def b := 1\n")
    _write(tmp_path / "A/Impl/Three.lean", "def c := 1\n")
    res = check_unsafe_keyword(
        tmp_path, ["A/Impl/One.lean", "A/Impl/Two.lean", "A/Impl/Three.lean"]
    )
    assert res.detected
    assert res.files == ["A/Impl/One.lean", "A/Impl/Two.lean"]


def test_missing_file_skipped(tmp_path: Path) -> None:
    """Files referenced in the artifact but absent from the sandbox are skipped silently."""
    res = check_unsafe_keyword(tmp_path, ["A/Impl/NoSuch.lean"])
    assert not res.detected


# ─── grade_specs integration: unsafe_detected short-circuits every spec ───


def _mk_artifact(bench: Benchmark, mode: str) -> Artifact:
    """Minimal artifact with sorry-filled slots for every spec/kind."""
    kinds = ("prove", "disprove") if mode == "proof" else ("prove", "unsat", "sat")
    slots: list[ExtractedSlot] = []
    for m in bench.iter_modules():
        for spec in m.specs:
            bare = spec.removeprefix("spec_")
            for k in kinds:
                slots.append(
                    ExtractedSlot(
                        file="x/Proof/x.lean",
                        prefix="benchmark",
                        key="proof",
                        def_name=f"{k}_{bare}",
                        expected_kind=k,
                        expected_target=spec,
                        found=True,
                        body_lines=["  sorry"],
                        body_hash="",
                        is_empty=False,
                        contains_sorry=True,
                        contains_axiom=False,
                        contains_admit=False,
                        actual_fields={},
                        start_line=1,
                        end_line=2,
                        error="",
                    )
                )
    return Artifact(
        benchmark_id="bank_ledger_reference",
        mode=mode,
        sandbox_dir="/tmp/fake",
        slots=slots,
    )


def test_grade_specs_unsafe_detected_fails_every_spec() -> None:
    bench = Benchmark(REF)
    artifact = _mk_artifact(bench, "proof")
    results, summary = grade_specs(
        bench,
        artifact,
        axioms=[],
        mode="proof",
        unsafe_detected=True,
        unsafe_reason="`unsafe` keyword in BankLedger/Impl/Account.lean",
    )
    assert summary.passed_specs == 0
    assert summary.failed_specs == summary.total_specs
    assert all(r.status == "unsafe_keyword" for r in results)
    assert any("unsafe" in r.notes for r in results)
