"""Tests for the lean_spec workflow + lean_extract helpers."""

from __future__ import annotations

from pathlib import Path

from vero.curation.lean_extract import (
    enumerate_executables,
    enumerate_theorems,
    reshape_theorem_to_spec,
)
from vero.curation.models import SourceLanguage
from vero.curation.pipeline import (
    LeanSpecPipeline,
    PythonSpecPipeline,
    get_pipeline,
)
from vero.curation.stages.spec_write import SpecWriteStage

# ─── enumerate_theorems ─────────────────────────────────────────────


def test_enumerate_theorems_basic() -> None:
    src = """
import Foo

theorem ledger_create_zero (id : AccountId) (l : Ledger) :
    ¬ accountExists id l →
    getBalance id (createAccount id l) = some 0 := by
  intros; simp

lemma transfer_preserves_total (a b : AccountId) (amt : Balance) (l : Ledger) :
    totalAssets (transfer a b amt l) = totalAssets l := by
  intros; rfl
"""
    decls = enumerate_theorems(src)
    assert len(decls) == 2
    assert decls[0].name == "ledger_create_zero"
    assert "accountExists" in decls[0].sig
    assert "createAccount" in decls[0].sig
    assert decls[1].name == "transfer_preserves_total"
    assert "totalAssets" in decls[1].sig


def test_enumerate_theorems_skips_proof_term_internals() -> None:
    """Theorem extraction shouldn't be confused by `theorem` inside a `by` block."""
    src = """
theorem outer : True := by
  -- comment mentioning the word theorem
  trivial
"""
    decls = enumerate_theorems(src)
    assert len(decls) == 1
    assert decls[0].name == "outer"


def test_enumerate_theorems_handles_attributes() -> None:
    src = """
@[simp]
theorem attr_thm : 1 + 1 = 2 := by rfl

@[simp, norm_cast]
lemma double_attr : True := trivial
"""
    decls = enumerate_theorems(src)
    assert {d.name for d in decls} == {"attr_thm", "double_attr"}


def test_enumerate_theorems_empty_source() -> None:
    assert enumerate_theorems("") == []


# ─── enumerate_executables ──────────────────────────────────────────


def test_enumerate_executables_finds_top_level_defs() -> None:
    src = """
def myFn (x : Nat) : Nat := x + 1
def Foo.bar (y : Int) : Int := y * 2
def spec_skip (_impl : RepoImpl) : Prop := True
def _internal (n : Nat) : Nat := n
"""
    decls = enumerate_executables(src)
    names = sorted(d.name for d in decls)
    assert names == ["Foo.bar", "myFn"]
    assert all(not d.name.startswith("spec_") for d in decls)
    assert all(not d.name.startswith("_") for d in decls)


def test_enumerate_executables_strips_namespace_for_helper_check() -> None:
    """`def Foo._helper` is a helper (tail starts with `_`), not an API."""
    src = """
def Foo._helper (x : Nat) : Nat := x
def Foo.public (y : Nat) : Nat := y
"""
    decls = enumerate_executables(src)
    assert {d.name for d in decls} == {"Foo.public"}


# ─── reshape_theorem_to_spec ────────────────────────────────────────


def test_reshape_theorem_to_spec_basic() -> None:
    decl = enumerate_theorems("theorem foo (n : Nat) : n + 0 = n := by simp")[0]
    spec = reshape_theorem_to_spec(decl)
    assert "def spec_foo (impl : RepoImpl) : Prop" in spec
    assert "n + 0 = n" in spec
    assert "by simp" not in spec  # proof dropped


def test_reshape_theorem_to_spec_already_prefixed() -> None:
    decl = enumerate_theorems("theorem spec_already_named : True := trivial")[0]
    spec = reshape_theorem_to_spec(decl)
    assert "def spec_already_named" in spec
    # Should not produce `def spec_spec_already_named`
    assert "spec_spec_already_named" not in spec


def test_reshape_theorem_with_empty_sig_falls_back() -> None:
    decl = enumerate_theorems("theorem bare := trivial")[0]
    spec = reshape_theorem_to_spec(decl)
    assert "def spec_bare (impl : RepoImpl) : Prop" in spec
    assert "True" in spec


# ─── workflow wiring ────────────────────────────────────────────────


def test_lean_spec_omits_spec_write() -> None:
    """LeanSpecPipeline must NOT include SpecWriteStage; PythonSpecPipeline does."""
    assert SpecWriteStage not in LeanSpecPipeline.stages
    assert SpecWriteStage in PythonSpecPipeline.stages


def test_get_pipeline_lean_spec(tmp_path: Path) -> None:
    from vero.curation.config import CurationConfig

    cfg = CurationConfig(
        benchmark_id="x",
        source_language=SourceLanguage.LEAN,
        source_dir=str(tmp_path),
        output_dir=str(tmp_path / "out"),
        workflow="lean_spec",
    )
    pipe = get_pipeline(cfg)
    assert isinstance(pipe, LeanSpecPipeline)
