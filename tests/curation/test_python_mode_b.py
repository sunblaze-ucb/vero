"""Tests for Python pipeline mode B (new-repo flow via discover→…→spec_write)."""

from __future__ import annotations

from pathlib import Path

import pytest

from vero.curation.models import SourceLanguage
from vero.curation.pipeline import PythonSpecPipeline, get_pipeline
from vero.curation.stages._skill_preamble import skill_preamble
from vero.curation.stages.init import detect_language

# ─── language detection ─────────────────────────────────────────────


def test_detect_language_python(tmp_path: Path) -> None:
    (tmp_path / "a.py").write_text("def foo(): pass\n")
    (tmp_path / "b.py").write_text("def bar(): pass\n")
    assert detect_language(tmp_path) == SourceLanguage.PYTHON


def test_detect_language_python_beats_zero_other(tmp_path: Path) -> None:
    """If there's only python source, we shouldn't fall through to ValueError."""
    (tmp_path / "x.py").write_text("x = 1\n")
    assert detect_language(tmp_path) == SourceLanguage.PYTHON


def test_detect_language_dafny_still_wins_when_present(tmp_path: Path) -> None:
    """A repo with both .py and .dfy should pick the dominant kind."""
    for i in range(5):
        (tmp_path / f"d{i}.dfy").write_text("// dafny\n")
    (tmp_path / "x.py").write_text("# python helper\n")
    assert detect_language(tmp_path) == SourceLanguage.DAFNY


def test_detect_language_lean(tmp_path: Path) -> None:
    """Lean source mode: .lean files but no lakefile.toml at the root."""
    (tmp_path / "Main.lean").write_text("def f := 1\n")
    (tmp_path / "Aux.lean").write_text("def g := 2\n")
    assert detect_language(tmp_path) == SourceLanguage.LEAN


def test_detect_language_lean_skipped_with_lakefile(tmp_path: Path) -> None:
    """A directory with a lakefile.toml is the curator's *output*, not source."""
    (tmp_path / "lakefile.toml").write_text("[package]\nname='X'\n")
    (tmp_path / "Main.lean").write_text("def f := 1\n")
    # Should NOT detect as lean — falls through to "no sources" error
    with pytest.raises(ValueError):
        detect_language(tmp_path)


def test_detect_language_no_sources(tmp_path: Path) -> None:
    (tmp_path / "README.md").write_text("nothing here")
    with pytest.raises(ValueError):
        detect_language(tmp_path)


# ─── skill preamble for python ──────────────────────────────────────


def test_skill_preamble_python_discover() -> None:
    text = skill_preamble("discover", SourceLanguage.PYTHON)
    assert "vero-discover" in text
    assert "vero-source-python" in text


def test_skill_preamble_python_translate_includes_pitfalls() -> None:
    text = skill_preamble("translate", SourceLanguage.PYTHON)
    assert "vero-translate" in text
    assert "vero-source-python" in text
    assert "vero-python-pitfalls" in text
    assert "vero-lean-pitfalls" in text


def test_skill_preamble_lean_uses_lean_source_skill() -> None:
    text = skill_preamble("translate", SourceLanguage.LEAN)
    assert "vero-source-lean" in text
    # Lean-source mode skips a separate pitfalls skill; vero-lean-pitfalls
    # still loads as the generic Lean-target pitfall reference.
    assert "vero-lean-pitfalls" in text


# ─── workflow wiring ────────────────────────────────────────────────


def test_get_pipeline_python_spec(tmp_path: Path) -> None:
    from vero.curation.config import CurationConfig

    cfg = CurationConfig(
        benchmark_id="x",
        source_language=SourceLanguage.PYTHON,
        source_dir=str(tmp_path),
        output_dir=str(tmp_path / "out"),
        workflow="python_spec",
    )
    pipe = get_pipeline(cfg)
    assert isinstance(pipe, PythonSpecPipeline)
