"""Tests for ``vero.generation.render.render_sandbox``."""

from __future__ import annotations

from pathlib import Path

import pytest

from vero.generation.benchmark import Benchmark
from vero.generation.extractor import extract, load_slots
from vero.generation.render import render_sandbox
from vero.generation.sandbox import create_sandbox

REPO_ROOT = Path(__file__).resolve().parents[2]
REF = REPO_ROOT / "reference" / "BankLedger"


def test_render_from_untouched_sandbox_is_noop(tmp_path: Path) -> None:
    """Rendering from an artifact extracted from a pristine sandbox
    produces a sandbox byte-identical to the one create_sandbox makes."""
    source = tmp_path / "source"
    rendered = tmp_path / "rendered"
    create_sandbox(REF, source, mode="proof")
    artifact = extract(source, Benchmark(REF), mode="proof")
    render_sandbox(REF, artifact, rendered, mode="proof", overwrite=True)

    # File-by-file content compare, skipping sandbox-only scratch dirs.
    for path in source.rglob("*"):
        if path.is_dir():
            continue
        rel = path.relative_to(source)
        if rel.parts and rel.parts[0] in {".lake", "build", "eval", "eval_report"}:
            continue
        other = rendered / rel
        assert other.exists(), f"missing {rel} in rendered"
        assert path.read_bytes() == other.read_bytes(), f"byte mismatch on {rel}"


def test_render_overlays_agent_proof(tmp_path: Path) -> None:
    """Agent-filled proof bodies overlay cleanly onto a fresh sandbox."""
    source = tmp_path / "source"
    rendered = tmp_path / "rendered"
    create_sandbox(REF, source, mode="proof")

    # Simulate an agent filling prove_num_matches_list.
    target = source / "BankLedger/Proof/Ledger.lean"
    text = target.read_text()
    old = (
        "-- !benchmark @start proof def=prove_num_matches_list "
        "kind=prove target=spec_num_matches_list\n"
        "  sorry\n"
        "-- !benchmark @end proof def=prove_num_matches_list"
    )
    new = (
        "-- !benchmark @start proof def=prove_num_matches_list "
        "kind=prove target=spec_num_matches_list\n"
        "  intro ledger\n"
        "  simp [canonical, Bank.numAccounts, Bank.accountList, List.length_map]\n"
        "-- !benchmark @end proof def=prove_num_matches_list"
    )
    assert old in text
    target.write_text(text.replace(old, new))

    artifact = extract(source, Benchmark(REF), mode="proof")
    render_sandbox(REF, artifact, rendered, mode="proof", overwrite=True)

    rendered_target = rendered / "BankLedger/Proof/Ledger.lean"
    rendered_text = rendered_target.read_text()
    assert "intro ledger" in rendered_text
    assert "List.length_map" in rendered_text


def test_render_discards_frozen_file_tampering(tmp_path: Path) -> None:
    """If the agent tampered with a frozen file, the fresh render ignores it."""
    source = tmp_path / "source"
    rendered = tmp_path / "rendered"
    create_sandbox(REF, source, mode="proof")

    # Tamper with the Bundle (frozen): drop one field.
    bundle = source / "BankLedger/Bundle.lean"
    pristine_bundle = (REF / "BankLedger/Bundle.lean").read_bytes()
    bundle.write_text("-- tampered\n")

    artifact = extract(source, Benchmark(REF), mode="proof")
    render_sandbox(REF, artifact, rendered, mode="proof", overwrite=True)

    # Rendered Bundle must match the source benchmark, NOT the tampered copy.
    rendered_bundle = (rendered / "BankLedger/Bundle.lean").read_bytes()
    assert rendered_bundle == pristine_bundle
    assert b"-- tampered" not in rendered_bundle


def test_render_rejects_mode_mismatch(tmp_path: Path) -> None:
    source = tmp_path / "source"
    rendered = tmp_path / "rendered"
    create_sandbox(REF, source, mode="proof")
    artifact = extract(source, Benchmark(REF), mode="proof")
    with pytest.raises(ValueError):
        render_sandbox(REF, artifact, rendered, mode="codeproof", overwrite=True)


def test_render_drops_extras(tmp_path: Path) -> None:
    """Agent-added markers outside the schedule are not carried into the fresh sandbox."""
    source = tmp_path / "source"
    rendered = tmp_path / "rendered"
    create_sandbox(REF, source, mode="proof")

    # Inject a bogus marker pair.
    target = source / "BankLedger/Proof/Account.lean"
    text = target.read_text()
    text += (
        "\n-- !benchmark @start proof def=bogus_theorem "
        "kind=prove target=spec_create_zero_balance\n"
        "  trivial\n"
        "-- !benchmark @end proof def=bogus_theorem\n"
    )
    target.write_text(text)
    artifact = extract(source, Benchmark(REF), mode="proof")
    assert any(x.def_name == "bogus_theorem" for x in artifact.extras)

    render_sandbox(REF, artifact, rendered, mode="proof", overwrite=True)
    rendered_slots = load_slots(rendered / "BankLedger/Proof/Account.lean")
    names = {s.def_name for s in rendered_slots}
    assert "bogus_theorem" not in names
