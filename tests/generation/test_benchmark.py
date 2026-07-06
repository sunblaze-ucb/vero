"""Tests for ``vero.generation.benchmark``.

Uses ``reference/BankLedger/`` as the canonical fixture.
"""

from __future__ import annotations

from pathlib import Path

import pytest

from vero.generation.benchmark import (
    Benchmark,
    all_editable_files,
    load_slots,
    proof_editable_files,
)

REPO_ROOT = Path(__file__).resolve().parents[2]
REF = REPO_ROOT / "reference" / "BankLedger"


def test_benchmark_loads_manifest() -> None:
    b = Benchmark(REF)
    assert b.benchmark_id == "bank_ledger_reference"
    assert b.root_package == "BankLedger"
    assert "proof" in b.modes_supported
    assert "codeproof" in b.modes_supported
    assert len(b.packages) == 1
    pkg = b.packages[0]
    assert pkg.name == "BankLedger"
    assert pkg.bundle_type == "BankLedgerBundle"
    assert pkg.repo_impl_field == "bankLedger"
    assert len(pkg.modules) == 4
    names = [m.name for m in pkg.modules]
    assert names == ["Account", "Transaction", "Transfer", "Ledger"]


def test_module_apis_and_specs() -> None:
    b = Benchmark(REF)
    account = [m for m in b.iter_modules() if m.name == "Account"][0]
    api_names = [a.name for a in account.apis]
    assert "createAccount" in api_names
    assert "getBalance" in api_names
    assert "spec_create_zero_balance" in account.specs
    assert "spec_close_preserves_others" in account.specs


def test_rich_manifest_spec_entries_are_normalized(tmp_path: Path) -> None:
    """Curation manifests store spec metadata dicts; gen/eval needs only names."""
    import json

    bench = tmp_path / "RichSpecs"
    bench.mkdir()
    (bench / "manifest.json").write_text(
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
                                "name": "Core",
                                "impl": "RichSpecs/Impl/Core.lean",
                                "spec": "RichSpecs/Spec/Core.lean",
                                "apis": [],
                                "specs": [
                                    {
                                        "name": "spec_from_dict",
                                        "source_id": "src.dfy:lemma:1",
                                    },
                                    "spec_from_string",
                                ],
                            }
                        ],
                    }
                ],
            }
        )
    )

    module = next(Benchmark(bench).iter_modules())
    assert module.specs == ("spec_from_dict", "spec_from_string")


def test_paths_resolve_to_existing_files() -> None:
    b = Benchmark(REF)
    assert b.root_hub_path.is_file()
    assert b.harness_path.is_file()
    assert b.test_path.is_file()
    for m in b.iter_modules():
        assert m.impl_path(b.root).is_file(), f"impl missing for {m.name}"
        assert m.spec_path(b.root).is_file(), f"spec missing for {m.name}"


def test_load_slots_on_impl_account() -> None:
    b = Benchmark(REF)
    account = [m for m in b.iter_modules() if m.name == "Account"][0]
    slots = load_slots(account.impl_path(b.root))

    # Four code slots (createAccount, closeAccount, accountExists, getBalance)
    code_defs = sorted(s.def_name for s in slots if s.key == "code")
    assert code_defs == [
        "accountExists",
        "closeAccount",
        "createAccount",
        "getBalance",
    ]
    # code_aux companion pairs
    code_aux_defs = sorted(s.def_name for s in slots if s.key == "code_aux")
    assert code_aux_defs == code_defs
    # imports + global_aux (one each, no def)
    keys = [s.key for s in slots]
    assert keys.count("imports") == 1
    assert keys.count("global_aux") == 1


def test_slot_body_preserves_interior_lines() -> None:
    b = Benchmark(REF)
    account = [m for m in b.iter_modules() if m.name == "Account"][0]
    slots = load_slots(account.impl_path(b.root))
    create = [s for s in slots if s.key == "code" and s.def_name == "createAccount"][0]
    assert create.body, "expected at least one interior line"
    assert any("if ledger.any" in line for line in create.body)


def test_all_editable_files_are_impls() -> None:
    b = Benchmark(REF)
    files = all_editable_files(b)
    assert len(files) == 4
    for f in files:
        assert f.is_file()
        assert "/Impl/" in str(f)


def test_proof_editable_files_depend_on_mode() -> None:
    b = Benchmark(REF)
    pm = proof_editable_files(b, "proof")
    cp = proof_editable_files(b, "codeproof")
    assert len(pm) == 4
    assert len(cp) == 5
    assert str(cp[-1]).endswith("Proof/Joint.lean")


def test_missing_manifest_raises() -> None:
    with pytest.raises(FileNotFoundError):
        Benchmark(REF.parent)


def test_legacy_manifest_raises_with_helpful_hint(tmp_path) -> None:
    """Legacy pre-bundle manifests (task_index/file_map shape) get a clear refusal."""
    import json

    bench = tmp_path / "legacy"
    bench.mkdir()
    (bench / "manifest.json").write_text(
        json.dumps(
            {
                "benchmark_id": "old",
                "lean_version": "4.22.0",
                "source_language": "lean",
                "task_index": [],
            }
        )
    )
    with pytest.raises(ValueError, match="legacy pre-bundle manifest"):
        Benchmark(bench)


def test_manifest_missing_packages_without_task_index(tmp_path) -> None:
    """A manifest missing packages but without legacy markers still gets a clear error."""
    import json

    bench = tmp_path / "stripped"
    bench.mkdir()
    (bench / "manifest.json").write_text(
        json.dumps({"benchmark_id": "x", "lean_version": "4.29.1"})
    )
    with pytest.raises(ValueError, match="root_package"):
        Benchmark(bench)
