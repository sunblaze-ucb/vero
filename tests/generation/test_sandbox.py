"""Tests for ``vero.generation.sandbox.create_sandbox``."""

from __future__ import annotations

import shutil
from pathlib import Path

import pytest

from vero.generation.benchmark import Benchmark, load_slots
from vero.generation.sandbox import create_sandbox

REPO_ROOT = Path(__file__).resolve().parents[2]
REF = REPO_ROOT / "reference" / "BankLedger"


@pytest.fixture()
def sandbox(tmp_path: Path) -> Path:
    """Create a fresh `proof`-mode sandbox per-test under tmp_path."""
    out = tmp_path / "sandbox"
    yield out
    if out.exists():
        shutil.rmtree(out, ignore_errors=True)


def test_sandbox_proof_mode_layout(sandbox: Path) -> None:
    res = create_sandbox(REF, sandbox, mode="proof", strip_manifest=False)
    assert res.sandbox_dir == sandbox
    assert res.mode == "proof"

    # All Impl/Spec/Bundle/Harness/Test copied.
    b = Benchmark(sandbox)
    assert b.harness_path.is_file()
    assert b.root_hub_path.is_file()
    for m in b.iter_modules():
        assert m.impl_path(b.root).is_file()
        assert m.spec_path(b.root).is_file()

    # Proof/<Module>.lean materialized (proof mode → no Joint.lean)
    for m in b.iter_modules():
        assert (b.root / m.proof_rel()).is_file()
    assert not (b.root / b.joint_file_rel()).exists()

    # No Proof.lean aggregator; root hub does not import it.
    assert not (b.root / f"{b.root_package}/Proof.lean").exists()
    assert f"import {b.root_package}.Proof" not in b.root_hub_path.read_text()


def test_sandbox_links_lake_packages_cache(tmp_path: Path) -> None:
    bench = tmp_path / "bench"
    shutil.copytree(
        REF,
        bench,
        ignore=shutil.ignore_patterns(".lake", "build", ".git", "__pycache__"),
    )
    packages = bench / ".lake" / "packages"
    (packages / "dep").mkdir(parents=True)
    (packages / "dep" / "Dep.lean").write_text("-- cached dependency\n")
    (packages / "proofwidgets" / "widget").mkdir(parents=True)
    (packages / "proofwidgets" / "widget" / "package-lock.json").write_text("{}\n")

    out = tmp_path / "sandbox"
    create_sandbox(bench, out, mode="proof", strip_manifest=False)

    linked_packages = out / ".lake" / "packages"
    assert linked_packages.is_dir()

    linked_dep = linked_packages / "dep"
    assert linked_dep.is_symlink()
    assert linked_dep.resolve() == (packages / "dep").resolve()
    assert (linked_dep / "Dep.lean").is_file()

    copied_proofwidgets = linked_packages / "proofwidgets"
    assert copied_proofwidgets.is_dir()
    assert not copied_proofwidgets.is_symlink()
    assert (copied_proofwidgets / "widget" / "package-lock.json").is_file()


def test_sandbox_codeproof_mode_materializes_joint(sandbox: Path) -> None:
    create_sandbox(REF, sandbox, mode="codeproof", strip_manifest=False)
    b = Benchmark(sandbox)
    assert b.joint_file_path().is_file()
    text = b.joint_file_path().read_text()
    assert "!solution @start def=joint_unsatisfiability" in text
    # No aggregator is emitted; the evaluator compiles each proof file on its own.
    assert not (b.root / f"{b.root_package}/Proof.lean").exists()


def test_sandbox_proof_mode_keeps_impl_bodies(sandbox: Path) -> None:
    """Proof mode → reference implementations must stay intact inside code markers."""
    create_sandbox(REF, sandbox, mode="proof", strip_manifest=False)
    b = Benchmark(sandbox)
    account = [m for m in b.iter_modules() if m.name == "Account"][0]
    slots = load_slots(account.impl_path(b.root))
    create = [s for s in slots if s.key == "code" and s.def_name == "createAccount"][0]
    # Body should contain the reference impl — NOT just ``sorry``.
    joined = "\n".join(create.body)
    assert "if ledger.any" in joined
    assert joined.strip() != "sorry"


def test_sandbox_codeproof_blanks_impl_code_slots(sandbox: Path) -> None:
    """Codeproof mode → every code slot replaced with a single ``sorry``."""
    create_sandbox(REF, sandbox, mode="codeproof", strip_manifest=False)
    b = Benchmark(sandbox)
    for m in b.iter_modules():
        slots = load_slots(m.impl_path(b.root))
        for s in slots:
            if s.key == "code":
                # Interior should be exactly one line: "  sorry"
                stripped = [ln.rstrip() for ln in s.body if ln.strip()]
                assert stripped == ["  sorry"], (
                    f"{m.name}:{s.def_name} body = {s.body!r}"
                )


def test_sandbox_strips_curation_lines(sandbox: Path) -> None:
    create_sandbox(REF, sandbox, mode="proof", strip_manifest=False)
    b = Benchmark(sandbox)
    for m in b.iter_modules():
        text = m.impl_path(b.root).read_text()
        assert "!curation" not in text, f"found !curation in {m.name}"


def test_sandbox_instruction_file_exists(sandbox: Path) -> None:
    res = create_sandbox(REF, sandbox, mode="codeproof")
    assert res.instruction_file.is_file()
    text = res.instruction_file.read_text()
    assert "codeproof mode" in text
    assert "BankLedger" in text


def test_sandbox_overwrite_flag(sandbox: Path) -> None:
    create_sandbox(REF, sandbox, mode="proof")
    with pytest.raises(FileExistsError):
        create_sandbox(REF, sandbox, mode="proof")
    create_sandbox(REF, sandbox, mode="codeproof", overwrite=True, strip_manifest=False)
    b = Benchmark(sandbox)
    assert b.joint_file_path().is_file()


def test_sandbox_strips_manifest_by_default(sandbox: Path) -> None:
    """``create_sandbox`` removes manifest.json from the agent-visible sandbox."""
    create_sandbox(REF, sandbox, mode="proof")
    assert not (sandbox / "manifest.json").exists()


def test_sandbox_keeps_manifest_when_asked(sandbox: Path) -> None:
    create_sandbox(REF, sandbox, mode="proof", strip_manifest=False)
    assert (sandbox / "manifest.json").exists()


def test_sandbox_instruction_no_feedback_by_default(sandbox: Path) -> None:
    """Single-shot (no feedback) rendering must not emit the feedback block."""
    res = create_sandbox(REF, sandbox, mode="proof")
    text = res.instruction_file.read_text()
    assert "Previous iteration feedback" not in text
    assert not (sandbox / "FEEDBACK.md").exists()


def test_sandbox_instruction_with_feedback(sandbox: Path) -> None:
    """When ``previous_feedback`` is set, INSTRUCTION gains the block
    and ``FEEDBACK.md`` appears at the sandbox root."""
    sample = "# Report\n\npassed 3/11"
    res = create_sandbox(
        REF,
        sandbox,
        mode="proof",
        previous_feedback=sample,
        iteration_index=1,
        iteration_total=3,
    )
    text = res.instruction_file.read_text()
    assert "Previous iteration feedback" in text
    assert "iteration **1 of 3**" in text
    assert "passed 3/11" in text
    # FEEDBACK.md lands at the sandbox root, not under a Lean project dir.
    fb = sandbox / "FEEDBACK.md"
    assert fb.is_file()
    assert fb.read_text() == sample


# ─── unscheduled impl slots ─────────────────────────────────

_UNSCHEDULED_HELPER = """
-- !benchmark @start code_aux def=frozenHelper
-- !benchmark @end code_aux def=frozenHelper

def frozenHelper : Nat :=
-- !benchmark @start code def=frozenHelper
  42
-- !benchmark @end code def=frozenHelper
"""


def _bench_with_unscheduled_slot(tmp_path: Path) -> Path:
    """BankLedger + a ``code`` slot whose ``def=`` is not a manifest API."""
    bench = tmp_path / "BankLedger"
    shutil.copytree(REF, bench, ignore=shutil.ignore_patterns(".lake", "build"))
    impl = bench / "BankLedger" / "Impl" / "Account.lean"
    impl.write_text(impl.read_text() + _UNSCHEDULED_HELPER)
    return bench


@pytest.mark.parametrize("mode", ["proof", "codeproof"])
def test_sandbox_freezes_unscheduled_impl_slots(tmp_path: Path, mode: str) -> None:
    """An unscheduled slot keeps its reference body as frozen code in both modes
    (regression: unicode's spec helpers were sorry'd in codeproof)."""
    from vero.generation.extractor import extract

    bench = _bench_with_unscheduled_slot(tmp_path)
    out = tmp_path / "sandbox"
    create_sandbox(bench, out, mode=mode, strip_manifest=False)

    text = (out / "BankLedger" / "Impl" / "Account.lean").read_text()
    assert "def frozenHelper : Nat :=\n  42\n" in text
    assert "def=frozenHelper" not in text
    assert extract(out, Benchmark(bench), mode=mode).extras == []
    if mode == "codeproof":
        # Scheduled API slots are still blanked.
        create = [
            s
            for s in load_slots(out / "BankLedger" / "Impl" / "Account.lean")
            if s.key == "code" and s.def_name == "createAccount"
        ]
        assert [ln.strip() for ln in create[0].body if ln.strip()] == ["sorry"]


# ─── trusted axioms in INSTRUCTION.md ───────────────────────


def test_instruction_lists_trusted_axioms(tmp_path: Path) -> None:
    import json

    from vero.generation.prompt import render_instruction

    bench = tmp_path / "BankLedger"
    shutil.copytree(REF, bench, ignore=shutil.ignore_patterns(".lake", "build"))
    manifest = json.loads((bench / "manifest.json").read_text())
    manifest["trusted_axioms"] = ["contract_induction", "Foo.bar"]
    (bench / "manifest.json").write_text(json.dumps(manifest))

    for mode in ("proof", "codeproof"):
        text = render_instruction(Benchmark(bench), mode=mode)
        assert "## Trusted axioms" in text
        assert "- ``contract_induction``" in text
        assert "- ``Foo.bar``" in text
        assert "plus this benchmark's trusted axioms" in text


def test_instruction_without_trusted_axioms_has_no_section() -> None:
    from vero.generation.prompt import render_instruction

    for mode in ("proof", "codeproof"):
        text = render_instruction(Benchmark(REF), mode=mode)
        assert "## Trusted axioms" not in text
        assert "plus this benchmark's trusted axioms" not in text
