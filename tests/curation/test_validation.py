"""Validation tests against the canonical reference benchmark."""

from __future__ import annotations

from pathlib import Path

import pytest

from vero.curation.validation import validate_benchmark
from vero.curation.validation.markers import (
    BENCHMARK_KEYS,
    pair_slots,
    parse_file_markers,
    parse_marker_line,
)

REPO_ROOT = Path(__file__).parent.parent.parent
REFERENCE = REPO_ROOT / "reference" / "BankLedger"


# ─── Full-benchmark validation ──────────────────────────────────────


def test_reference_validates_without_build() -> None:
    """Reference benchmark must pass all rule checks (skipping the slow `lake build`)."""
    report = validate_benchmark(REFERENCE, skip_build=True)
    assert report.overall in {"pass", "warn"}, (
        f"reference validation overall={report.overall}\nblockers: {report.blockers}"
    )
    assert not report.blockers, f"unexpected blockers: {report.blockers}"


def test_reference_schema_pass() -> None:
    report = validate_benchmark(REFERENCE, skip_build=True)
    assert report.rule_checks["manifest_schema"].status == "pass"


def test_reference_manifest_vs_code_pass() -> None:
    report = validate_benchmark(REFERENCE, skip_build=True)
    check = report.rule_checks["manifest_vs_code"]
    assert check.status in {"pass", "warn"}, (
        f"manifest_vs_code={check.status}; details={check.details}"
    )


def test_reference_markers_grammar_pass() -> None:
    report = validate_benchmark(REFERENCE, skip_build=True)
    assert report.rule_checks["markers_grammar"].status == "pass", [
        f.message for f in report.rule_checks["markers_grammar"].details
    ]


def test_reference_markers_positioning_pass() -> None:
    report = validate_benchmark(REFERENCE, skip_build=True)
    assert report.rule_checks["markers_positioning"].status in {"pass", "warn"}, [
        f.message for f in report.rule_checks["markers_positioning"].details
    ]


def test_marker_free_frozen_impl_positioning_passes(tmp_path: Path) -> None:
    """A no-API Impl module may be frozen marker-free without failing positioning."""
    import json as _json
    import shutil

    from vero.curation.validation.checks import (
        check_file_roles,
        check_markers_positioning,
    )

    bench = tmp_path / "BankLedger"
    shutil.copytree(REFERENCE, bench, ignore=shutil.ignore_patterns(".lake", "build"))

    impl_rel = "BankLedger/Impl/Frozen.lean"
    spec_rel = "BankLedger/Spec/Frozen.lean"
    (bench / impl_rel).write_text(
        "import BankLedger.Impl.Account\n\n"
        "/-- Frozen helper vocabulary with no fillable APIs. -/\n"
        "def frozenHelper : Nat := 0\n"
    )
    (bench / spec_rel).write_text(
        "import BankLedger.Harness\n\nnamespace BankLedger\n\nend BankLedger\n"
    )

    manifest_path = bench / "manifest.json"
    manifest = _json.loads(manifest_path.read_text())
    manifest["packages"][0]["modules"].append(
        {
            "name": "Frozen",
            "impl": impl_rel,
            "spec": spec_rel,
            "apis": [],
            "specs": [],
        }
    )
    manifest_path.write_text(_json.dumps(manifest, indent=2))

    assert check_markers_positioning(bench).status == "pass"
    assert check_file_roles(bench).status == "pass"


def test_source_alignment_inactive_for_handcrafted_reference() -> None:
    """The source-alignment gate should not break the hand-written reference."""
    from vero.curation.validation.checks import check_source_alignment

    result = check_source_alignment(REFERENCE)
    assert result.status == "pass"
    assert any("not marked translated" in f.message for f in result.details)


def test_source_alignment_warns_on_missing_translated_manifest_source(
    tmp_path: Path,
) -> None:
    """Translated manifest items without provenance should be visible again."""
    import json as _json
    import shutil

    from vero.curation.validation.checks import check_source_alignment

    bench = tmp_path / "BankLedger"
    shutil.copytree(REFERENCE, bench, ignore=shutil.ignore_patterns(".lake", "build"))
    manifest_path = bench / "manifest.json"
    manifest = _json.loads(manifest_path.read_text())
    manifest["source"]["kind"] = "translated"
    manifest["source"]["language"] = "dafny"
    manifest_path.write_text(_json.dumps(manifest))

    result = check_source_alignment(bench)

    assert result.status == "warn"
    assert any(
        "translated manifest item(s) lack source provenance" in f.message
        for f in result.details
    )


def test_reference_file_roles_pass() -> None:
    report = validate_benchmark(REFERENCE, skip_build=True)
    assert report.rule_checks["file_roles"].status == "pass", [
        f.message for f in report.rule_checks["file_roles"].details
    ]


def test_reference_guards_pass() -> None:
    report = validate_benchmark(REFERENCE, skip_build=True)
    assert report.rule_checks["guards"].status == "pass"


def test_guards_do_not_count_check_as_api_coverage(tmp_path: Path) -> None:
    """A bare #check mentions an API but does not exercise behavior."""
    import json as _json

    from vero.curation.validation.checks import check_guards

    bench = tmp_path / "bench"
    (bench / "Pkg").mkdir(parents=True)
    (bench / "Pkg" / "Test.lean").write_text("#check Bank.send\n#guard True\n")
    (bench / "manifest.json").write_text(
        _json.dumps(
            {
                "files": {"test": "Pkg/Test.lean"},
                "packages": [
                    {
                        "name": "Pkg",
                        "modules": [
                            {
                                "name": "Io",
                                "apis": [{"name": "send", "kind": "api"}],
                            }
                        ],
                    }
                ],
            }
        )
    )

    result = check_guards(bench)
    assert result.status == "warn"
    assert any("send" in f.message for f in result.details)


def test_reference_toolchain_pass() -> None:
    report = validate_benchmark(REFERENCE, skip_build=True)
    assert report.rule_checks["toolchain"].status == "pass"


def test_reference_spec_shape_pass() -> None:
    report = validate_benchmark(REFERENCE, skip_build=True)
    check = report.rule_checks["spec_shape"]
    assert check.status == "pass", [f.message for f in check.details]


def test_hardstop_skips_downstream_when_manifest_schema_fails(tmp_path: Path) -> None:
    """A manifest missing core fields causes downstream checks to skip rather than false-pass."""
    import json as _json

    from vero.curation.validation.checks import run_rule_checks

    bench = tmp_path / "bench"
    bench.mkdir()
    # Old-format manifest (lean-regex shape): no `packages`, no `files`, no
    # `modes_supported`, no `curation`. Schema check fails.
    (bench / "manifest.json").write_text(
        _json.dumps(
            {
                "benchmark_id": "old_format",
                "lean_version": "4.22.0",
                "source_language": "lean",
                "task_index": [],
            }
        )
    )
    results = run_rule_checks(bench, skip_build=True)
    assert results["manifest_schema"].status == "fail"
    for name in (
        "manifest_vs_code",
        "markers_grammar",
        "markers_positioning",
        "file_roles",
        "spec_shape",
        "spec_quality",
        "api_spec_coverage",
        "provenance",
        "trusted_boundary",
        "source_index",
        "source_coverage",
        "entity_roles",
        "reference_consistency",
        "trusted_surface",
        "import_delta",
        "policy_artifacts",
        "plan_source_references",
        "semantic_weakening",
        "plan_placeholder_bodies",
        "guards",
    ):
        assert results[name].status == "skipped", (
            f"{name} should be skipped when manifest_schema fails, got "
            f"{results[name].status}"
        )
    # toolchain still runs (doesn't depend on manifest packages).
    assert results["toolchain"].status in {"pass", "fail", "warn"}


def test_reference_source_coverage_warn_when_discover_missing() -> None:
    """Hand-crafted benchmark has no discover.json; coverage check warns and skips."""
    report = validate_benchmark(REFERENCE, skip_build=True)
    check = report.rule_checks["source_coverage"]
    assert check.status == "warn"
    assert any("discover.json" in f.message for f in check.details)


def test_source_coverage_reads_current_curation_discovery_report(
    tmp_path: Path,
) -> None:
    """Coverage lookup must find `curation/discovery_report.json`, not only `.vero/discover.json`."""
    import json as _json
    import shutil

    from vero.curation.validation.checks import check_source_coverage

    workspace = tmp_path / "workspace"
    bench = workspace / "lean_output" / "BankLedger"
    shutil.copytree(REFERENCE, bench)
    curation = workspace / "curation"
    curation.mkdir()
    (curation / "discovery_report.json").write_text(
        _json.dumps(
            {
                "items": [
                    {
                        "name": "definitelyMissing",
                        "lean_name": "definitelyMissing",
                        "category": "exec-fn",
                        "selected": True,
                    }
                ]
            }
        )
    )

    result = check_source_coverage(bench)
    assert result.status == "warn"
    assert any("definitelyMissing" in f.message for f in result.details)


def test_source_coverage_matches_selected_items_by_source_id(tmp_path: Path) -> None:
    """Renamed source items should round-trip by source_id, not only Lean name."""
    import json as _json
    import shutil

    from vero.curation.validation.checks import check_source_coverage

    workspace = tmp_path / "workspace"
    bench = workspace / "lean_output" / "BankLedger"
    shutil.copytree(REFERENCE, bench)

    manifest_path = bench / "manifest.json"
    manifest = _json.loads(manifest_path.read_text())
    manifest["packages"][0]["modules"][0]["apis"][0]["source_id"] = (
        "src.dfy:SourceName:12"
    )
    manifest_path.write_text(_json.dumps(manifest))

    vero = workspace / ".vero"
    vero.mkdir()
    (vero / "source_index.json").write_text(
        _json.dumps(
            {
                "version": 1,
                "entities": [
                    {
                        "id": "src.dfy:SourceName:12",
                        "name": "SourceName",
                        "qualified_name": "SourceName",
                        "kind": "method",
                        "source_file": "src.dfy",
                        "source_line": 12,
                        "selected": True,
                    }
                ],
            }
        )
    )

    result = check_source_coverage(bench)

    assert result.status == "pass"
    assert any("round-tripped" in f.message for f in result.details)


def test_source_coverage_prefers_selection_plan_over_raw_source_index(
    tmp_path: Path,
) -> None:
    """Raw source index inventory should not force dropped selection items into manifest."""
    import json as _json
    import shutil

    from vero.curation.validation.checks import check_source_coverage

    workspace = tmp_path / "workspace"
    bench = workspace / "lean_output" / "BankLedger"
    shutil.copytree(REFERENCE, bench)

    manifest_path = bench / "manifest.json"
    manifest = _json.loads(manifest_path.read_text())
    manifest["packages"][0]["modules"][0]["apis"][0]["source_id"] = (
        "src.dfy:Selected:12"
    )
    manifest_path.write_text(_json.dumps(manifest))

    vero = workspace / ".vero"
    vero.mkdir()
    (vero / "source_index.json").write_text(
        _json.dumps(
            {
                "version": 1,
                "entities": [
                    {
                        "id": "src.dfy:Selected:12",
                        "name": "Selected",
                        "qualified_name": "Selected",
                        "kind": "method",
                        "source_file": "src.dfy",
                        "source_line": 12,
                        "selected": True,
                    },
                    {
                        "id": "src.dfy:DroppedHelper:20",
                        "name": "DroppedHelper",
                        "qualified_name": "DroppedHelper",
                        "kind": "lemma",
                        "source_file": "src.dfy",
                        "source_line": 20,
                        "selected": True,
                    },
                ],
            }
        )
    )
    curation = workspace / "curation"
    curation.mkdir()
    (curation / "selection_plan.json").write_text(
        _json.dumps(
            {
                "selected_items": [
                    {
                        "name": "Selected",
                        "selected": True,
                        "selection_stage_role": "scored_api",
                        "source_index_id": "src.dfy:Selected:12",
                    },
                    {
                        "name": "DroppedHelper",
                        "selected": True,
                        "selection_stage_role": "dropped_with_reason",
                        "source_index_id": "src.dfy:DroppedHelper:20",
                    },
                ]
            }
        )
    )

    result = check_source_coverage(bench)

    assert result.status == "pass"
    assert any("1 selected item" in f.message for f in result.details)


def test_source_coverage_prefers_empty_selection_plan_over_inventory_index(
    tmp_path: Path,
) -> None:
    """source_index selected=True is registry inventory, not final selection approval."""
    import json as _json
    import shutil

    from vero.curation.validation.checks import check_source_coverage

    workspace = tmp_path / "workspace"
    bench = workspace / "lean_output" / "BankLedger"
    shutil.copytree(REFERENCE, bench)
    vero = bench / ".vero"
    vero.mkdir()
    (vero / "source_index.json").write_text(
        _json.dumps(
            {
                "version": 1,
                "entities": [
                    {
                        "id": "Source.dfy:InventoryOnly:1",
                        "name": "InventoryOnly",
                        "kind": "function",
                        "source_file": "Source.dfy",
                        "source_line": 1,
                        "default_role": "unclassified",
                        "disposition": "unclassified",
                        "selected": True,
                    }
                ],
            }
        )
    )
    (vero / "selection_plan.json").write_text(_json.dumps({"selected_items": []}))

    result = check_source_coverage(bench)
    assert result.status == "pass"
    assert any("0 selected" in f.message for f in result.details)


def test_source_coverage_matches_selection_by_source_id_after_rename(
    tmp_path: Path,
) -> None:
    """Coverage should not depend on stale select-stage Lean names."""
    import json as _json
    import shutil

    from vero.curation.validation.checks import check_source_coverage

    workspace = tmp_path / "workspace"
    bench = workspace / "lean_output" / "BankLedger"
    shutil.copytree(REFERENCE, bench)
    manifest = _json.loads((bench / "manifest.json").read_text())
    manifest["packages"][0]["modules"][0].setdefault("apis", []).append(
        {
            "name": "finalName",
            "source_id": "Source.dfy:SelectedThing:1",
        }
    )
    (bench / "manifest.json").write_text(_json.dumps(manifest, indent=2))
    vero = bench / ".vero"
    vero.mkdir()
    (vero / "selection_plan.json").write_text(
        _json.dumps(
            {
                "selected_items": [
                    {
                        "selection_role": "scored_api",
                        "category": "api",
                        "lean_name": "staleSelectName",
                        "name": "SelectedThing",
                        "stable_source_id": "Source.dfy:SelectedThing:1",
                    }
                ]
            }
        )
    )

    result = check_source_coverage(bench)
    assert result.status == "pass"


def test_source_index_passes_valid_registry(tmp_path: Path) -> None:
    """A well-formed source index should pass the dedicated artifact check."""
    import json as _json
    import shutil

    from vero.curation.validation.checks import check_source_index

    workspace = tmp_path / "workspace"
    source = workspace / "source"
    source.mkdir(parents=True)
    (source / "Huffman.v").write_text("Definition build_fun := 1.\n")
    bench = workspace / "lean_output" / "BankLedger"
    shutil.copytree(REFERENCE, bench)
    vero = workspace / ".vero"
    vero.mkdir()
    (vero / "source_index.json").write_text(
        _json.dumps(
            {
                "version": 1,
                "generated_at": "2026-05-27T00:00:00Z",
                "source_language": "coq",
                "source_path": str(source),
                "entities": [
                    {
                        "id": "Huffman.v:build_fun:0",
                        "name": "build_fun",
                        "qualified_name": "build_fun",
                        "kind": "Definition",
                        "source_file": "Huffman.v",
                        "source_line": 1,
                        "signature": "Definition build_fun := 1.",
                        "default_role": "unclassified",
                        "disposition": "unclassified",
                        "selected": True,
                        "dependencies": [],
                    },
                    {
                        "id": "Huffman.v:build_fun_spec:1",
                        "name": "build_fun_spec",
                        "qualified_name": "build_fun_spec",
                        "kind": "Theorem",
                        "source_file": "Huffman.v",
                        "source_line": 1,
                        "signature": "Theorem build_fun_spec : True.",
                        "role": "scored_spec",
                        "disposition": "scored",
                        "selected": True,
                        "dependencies": [],
                    },
                ],
            }
        )
    )

    result = check_source_index(bench)
    assert result.status == "pass", [f.message for f in result.details]


def test_source_index_fails_malformed_entities(tmp_path: Path) -> None:
    """Schema/identity problems are hard errors."""
    import json as _json
    import shutil

    from vero.curation.validation.checks import check_source_index

    workspace = tmp_path / "workspace"
    bench = workspace / "lean_output" / "BankLedger"
    shutil.copytree(REFERENCE, bench)
    vero = workspace / ".vero"
    vero.mkdir()
    (vero / "source_index.json").write_text(
        _json.dumps(
            {
                "version": 2,
                "source_language": "coq",
                "source_path": str(workspace / "source"),
                "entities": [
                    {
                        "id": "dup",
                        "name": "bad",
                        "kind": "Definition",
                        "source_file": "../Bad.v",
                        "source_line": 0,
                        "default_role": "not_a_role",
                        "disposition": "axiomatized",
                        "dependencies": "not-a-list",
                    },
                    {
                        "id": "dup",
                        "name": "bad2",
                        "kind": "Definition",
                        "source_file": "Bad.v",
                        "source_line": 1,
                        "default_role": "unclassified",
                        "disposition": "unclassified",
                    },
                ],
            }
        )
    )

    result = check_source_index(bench)
    messages = [f.message for f in result.details]
    assert result.status == "fail"
    assert any("version must be 1" in m for m in messages)
    assert any("relative path" in m for m in messages)
    assert any("source_line must be a positive integer" in m for m in messages)
    assert any("unknown role" in m for m in messages)
    assert any("duplicate source_index entity id" in m for m in messages)
    assert any("dependencies must be a list" in m for m in messages)


def test_source_index_warns_on_missing_metadata_and_unknown_dependency(
    tmp_path: Path,
) -> None:
    """Incomplete but parseable source indexes produce warnings, not blockers."""
    import json as _json
    import shutil

    from vero.curation.validation.checks import check_source_index

    workspace = tmp_path / "workspace"
    source = workspace / "source"
    source.mkdir(parents=True)
    bench = workspace / "lean_output" / "BankLedger"
    shutil.copytree(REFERENCE, bench)
    vero = workspace / ".vero"
    vero.mkdir()
    (vero / "source_index.json").write_text(
        _json.dumps(
            {
                "version": 1,
                "entities": [
                    {
                        "id": "Demo.v:foo:0",
                        "name": "foo",
                        "kind": "Definition",
                        "source_file": "Demo.v",
                        "source_line": 3,
                        "default_role": "unclassified",
                        "disposition": "unclassified",
                        "dependencies": ["Demo.v:missing:1"],
                    }
                ],
            }
        )
    )

    result = check_source_index(bench)
    messages = [f.message for f in result.details]
    assert result.status == "warn"
    assert any("missing source_language" in m for m in messages)
    assert any("missing generated_at" in m for m in messages)
    assert any("missing source_path" in m for m in messages)
    assert any("dependency id" in m for m in messages)


def test_source_index_fails_selected_dependency_closure_breaks(tmp_path: Path) -> None:
    """Selected source items must not depend on missing or dropped source ids."""
    import json as _json
    import shutil

    from vero.curation.validation.checks import check_source_index

    workspace = tmp_path / "workspace"
    source = workspace / "source"
    source.mkdir(parents=True)
    (source / "Demo.v").write_text("Definition kept := 1.\nDefinition dropped := 2.\n")
    bench = workspace / "lean_output" / "BankLedger"
    shutil.copytree(REFERENCE, bench)
    vero = workspace / ".vero"
    vero.mkdir()
    (vero / "source_index.json").write_text(
        _json.dumps(
            {
                "version": 1,
                "generated_at": "2026-06-01T00:00:00Z",
                "source_language": "coq",
                "source_path": str(source),
                "entities": [
                    {
                        "id": "Demo.v:kept:1",
                        "name": "kept",
                        "kind": "Definition",
                        "source_file": "Demo.v",
                        "source_line": 1,
                        "default_role": "unclassified",
                        "disposition": "unclassified",
                        "selected": True,
                        "dependencies": ["Demo.v:missing:99", "Demo.v:dropped:2"],
                    },
                    {
                        "id": "Demo.v:dropped:2",
                        "name": "dropped",
                        "kind": "Definition",
                        "source_file": "Demo.v",
                        "source_line": 2,
                        "role": "dropped_with_reason",
                        "disposition": "unclassified",
                        "selected": False,
                        "drop_reason": "outside selected closure",
                        "dependencies": [],
                    },
                ],
            }
        )
    )

    result = check_source_index(bench)
    messages = [f.message for f in result.details]
    assert result.status == "fail"
    assert any("not present in source_index" in m for m in messages)
    assert any("dropped or unselected" in m for m in messages)


def test_entity_roles_requires_source_index_roles(tmp_path: Path) -> None:
    """The no-LLM source index is only useful if every entity is role-classified."""
    import json as _json
    import shutil

    from vero.curation.validation.checks import check_entity_roles

    workspace = tmp_path / "workspace"
    bench = workspace / "lean_output" / "BankLedger"
    shutil.copytree(REFERENCE, bench)
    vero = workspace / ".vero"
    vero.mkdir()
    (vero / "source_index.json").write_text(
        _json.dumps({"entities": [{"name": "F2R", "kind": "definition"}]})
    )

    result = check_entity_roles(bench)
    assert result.status == "fail"
    assert any("missing role" in f.message for f in result.details)


def test_reference_consistency_rejects_frozen_api_reference(tmp_path: Path) -> None:
    """Specs for API items must use impl.* references, not frozen namespace defs."""
    import shutil

    from vero.curation.validation.checks import check_reference_consistency

    dst = tmp_path / "bench"
    shutil.copytree(REFERENCE, dst)
    spec_file = dst / "BankLedger" / "Spec" / "Account.lean"
    spec_file.write_text(
        spec_file.read_text()
        + "\ndef spec_bad_frozen_reference (impl : RepoImpl) : Prop :=\n"
        + "  Bank.createAccount 0 [] = []\n"
    )

    result = check_reference_consistency(dst)
    assert result.status == "fail"
    assert any("Bank.createAccount" in f.message for f in result.details)


def test_reference_consistency_rejects_bare_api_reference(tmp_path: Path) -> None:
    """Specs must not mention API symbols directly without RepoImpl."""
    import shutil

    from vero.curation.validation.checks import check_reference_consistency

    dst = tmp_path / "bench"
    shutil.copytree(REFERENCE, dst)
    spec_file = dst / "BankLedger" / "Spec" / "Account.lean"
    spec_file.write_text(
        spec_file.read_text()
        + "\ndef spec_bad_bare_reference (impl : RepoImpl) : Prop :=\n"
        + "  createAccount 0 [] = []\n"
    )

    result = check_reference_consistency(dst)
    assert result.status == "fail"
    assert any("as 'createAccount'" in f.message for f in result.details)


def test_reference_consistency_accepts_impl_rooted_api_reference(
    tmp_path: Path,
) -> None:
    """Any matching manifest API reference rooted at `impl.` is acceptable."""
    import shutil

    from vero.curation.validation.checks import check_reference_consistency

    dst = tmp_path / "bench"
    shutil.copytree(REFERENCE, dst)
    spec_file = dst / "BankLedger" / "Spec" / "Account.lean"
    spec_file.write_text(
        spec_file.read_text()
        + "\ndef spec_good_impl_reference (impl : RepoImpl) : Prop :=\n"
        + "  impl.bank.createAccount 0 [] = impl.bank.createAccount 0 []\n"
    )

    result = check_reference_consistency(dst)
    assert result.status == "pass"


def test_reference_consistency_ignores_manifest_spec_names(tmp_path: Path) -> None:
    """The checked symbol set is manifest APIs only, not spec declarations."""
    import shutil

    from vero.curation.validation.checks import check_reference_consistency

    dst = tmp_path / "bench"
    shutil.copytree(REFERENCE, dst)
    spec_file = dst / "BankLedger" / "Spec" / "Account.lean"
    spec_file.write_text(
        spec_file.read_text()
        + "\ndef spec_mentions_spec_name (impl : RepoImpl) : Prop :=\n"
        + "  spec_create_exists impl\n"
    )

    result = check_reference_consistency(dst)
    assert result.status == "pass"


def test_trusted_surface_rejects_untrusted_axiom_and_code_sorry(tmp_path: Path) -> None:
    """Axioms and sorry inside benchmark code are curation failures."""
    import shutil

    from vero.curation.validation.checks import check_trusted_surface

    dst = tmp_path / "bench"
    shutil.copytree(REFERENCE, dst)
    impl_file = dst / "BankLedger" / "Impl" / "Account.lean"
    text = impl_file.read_text()
    text = text.replace(
        "fun id ledger =>\n    if ledger.any",
        "sorry\n\naxiom fakeFact : True\n\n  fun id ledger =>\n    if ledger.any",
        1,
    )
    impl_file.write_text(text)

    result = check_trusted_surface(dst)
    assert result.status == "fail"
    messages = [f.message for f in result.details]
    assert any("untrusted axiom" in m for m in messages)
    assert any("sorry/admit" in m for m in messages)


def test_import_delta_rejects_root_hub_drop(tmp_path: Path) -> None:
    """Root import hub must import every manifest module."""
    import shutil

    from vero.curation.validation.checks import check_import_delta

    dst = tmp_path / "bench"
    shutil.copytree(REFERENCE, dst)
    root = dst / "BankLedger.lean"
    root.write_text(root.read_text().replace("import BankLedger.Spec.Account\n", ""))

    result = check_import_delta(dst)
    assert result.status == "fail"
    assert any("BankLedger.Spec.Account" in f.message for f in result.details)


def test_import_delta_rejects_alternate_generated_root(tmp_path: Path) -> None:
    """Generated modules must not be imported through a second root namespace."""
    import shutil

    from vero.curation.validation.checks import check_import_delta

    dst = tmp_path / "bench"
    shutil.copytree(REFERENCE, dst)
    spec = dst / "BankLedger" / "Spec" / "Account.lean"
    spec.write_text(
        spec.read_text().replace(
            "import BankLedger.Harness", "import Wrapper.Harness", 1
        )
    )

    result = check_import_delta(dst)
    assert result.status == "fail"
    assert any("non-canonical root" in f.message for f in result.details)


def test_import_delta_matches_source_path_suffixes(tmp_path: Path) -> None:
    """Plan/manifest source roots and source-index-relative paths should match."""
    import json as _json
    import shutil

    from vero.curation.validation.checks import check_import_delta

    dst = tmp_path / "bench"
    shutil.copytree(REFERENCE, dst)
    manifest = _json.loads((dst / "manifest.json").read_text())
    manifest["packages"][0]["modules"][0]["upstream_files"] = [
        "src/JSON/Utils/Cursors.dfy"
    ]
    (dst / "manifest.json").write_text(_json.dumps(manifest, indent=2))
    vero = dst / ".vero"
    vero.mkdir()
    (vero / "source_index.json").write_text(
        _json.dumps(
            {
                "version": 1,
                "entities": [
                    {
                        "id": "Utils/Cursors.dfy:SkipByte:7229",
                        "name": "SkipByte",
                        "kind": "method",
                        "source_file": "Utils/Cursors.dfy",
                        "source_line": 190,
                    }
                ],
            }
        )
    )

    result = check_import_delta(dst)
    assert result.status == "pass"


def test_semantic_weakening_requires_review_or_degrade(tmp_path: Path) -> None:
    """Decomposed/weaker source theorem translations need explicit review/degrade metadata."""
    import json as _json
    import shutil

    from vero.curation.validation.checks import check_semantic_weakening

    dst = tmp_path / "bench"
    shutil.copytree(REFERENCE, dst)
    manifest = _json.loads((dst / "manifest.json").read_text())
    manifest["semantic_mappings"] = [
        {
            "source_theorem": "F2R_mult",
            "translated_specs": ["spec_fmult_mantissa", "spec_fmult_exp"],
            "semantic_bridge_required": ["F2R_def", "bpow_add"],
            "equivalence_status": "weaker",
        }
    ]
    (dst / "manifest.json").write_text(_json.dumps(manifest, indent=2))

    result = check_semantic_weakening(dst)
    assert result.status == "fail"
    assert any("equivalence_status='weaker'" in f.message for f in result.details)


def test_semantic_weakening_uses_plan_metadata_over_manifest(
    tmp_path: Path,
) -> None:
    """Plan metadata is authoritative when manifest specs omit review annotations."""
    import json as _json
    import shutil

    from vero.curation.validation.checks import check_semantic_weakening

    dst = tmp_path / "bench"
    shutil.copytree(REFERENCE, dst)
    manifest = _json.loads((dst / "manifest.json").read_text())
    spec_entry = manifest["packages"][0]["modules"][0]["specs"][0]
    spec_name = spec_entry if isinstance(spec_entry, str) else spec_entry["name"]
    manifest["packages"][0]["modules"][0]["specs"][0] = {
        "name": spec_name,
        "equivalence_status": "weaker",
        "semantic_bridge_required": ["projection bridge"],
    }
    (dst / "manifest.json").write_text(_json.dumps(manifest, indent=2))

    vero = dst / ".vero"
    vero.mkdir()
    (vero / "plan.json").write_text(
        _json.dumps(
            {
                "packages": [
                    {
                        "name": "BankLedger",
                        "modules": [
                            {
                                "name": manifest["packages"][0]["modules"][0]["name"],
                                "specs": [
                                    {
                                        "name": spec_name,
                                        "equivalence_status": "weaker",
                                        "semantic_bridge_required": [
                                            "projection bridge"
                                        ],
                                        "review_status": "approved",
                                    }
                                ],
                            }
                        ],
                    }
                ]
            },
            indent=2,
        )
    )

    result = check_semantic_weakening(dst)
    assert result.status == "pass"
    assert not any(f.severity == "error" for f in result.details)


def test_semantic_weakening_blocks_promotion_scope_structural_surrogate(
    tmp_path: Path,
) -> None:
    """Reviewed exploratory surrogates must still block promotion-scope validation."""
    import json as _json
    import shutil

    from vero.curation.validation.checks import check_semantic_weakening

    dst = tmp_path / "bench"
    shutil.copytree(REFERENCE, dst)
    vero = dst / ".vero"
    vero.mkdir()
    (vero / "plan.json").write_text(
        _json.dumps(
            {
                "packages": [
                    {
                        "name": "BankLedger",
                        "modules": [
                            {
                                "name": "Account",
                                "specs": [
                                    {
                                        "name": "spec_structural_bridge",
                                        "source_theorem": "source.theorem",
                                        "equivalence_status": "weaker",
                                        "semantic_bridge_required": [
                                            "full extensional map/set bridge"
                                        ],
                                        "promotion_scope": True,
                                        "degrade_to_structural_surrogate": True,
                                        "review_status": "approved_for_exploratory_smoke",
                                    }
                                ],
                            }
                        ],
                    }
                ]
            },
            indent=2,
        )
    )

    result = check_semantic_weakening(dst)
    assert result.status == "fail"
    assert any("promotion-scope" in f.message for f in result.details)
    assert any("semantic_bridge_required" in f.message for f in result.details)


def test_policy_artifacts_accepts_blocked_draft_representation_policy(
    tmp_path: Path,
) -> None:
    """Draft policy artifacts are valid evidence only while blockers remain explicit."""
    import json as _json
    import shutil

    from vero.curation.validation.checks import check_policy_artifacts

    dst = tmp_path / "bench"
    shutil.copytree(REFERENCE, dst)
    policy_dir = dst / ".vero" / "representation_policies"
    policy_dir.mkdir(parents=True)
    (policy_dir / "ghost_view.json").write_text(
        _json.dumps(
            {
                "policy_id": "demo.ghost_view.v1",
                "status": "draft_blocked_pending_human_decision",
                "blocked_specs": ["spec_demo"],
                "promotion_effect": {
                    "may_clear_demo_blocker": False,
                    "requires_human_decision": True,
                },
            },
            indent=2,
        )
    )
    (dst / ".vero" / "plan.json").write_text(
        _json.dumps(
            {
                "packages": [
                    {
                        "name": "BankLedger",
                        "modules": [
                            {
                                "name": "Account",
                                "specs": [
                                    {
                                        "name": "spec_demo",
                                        "promotion_scope": True,
                                        "promotion_status": "blocked_pending_ghost_view_policy",
                                        "semantic_bridge_required": [
                                            "source ghost map bridge"
                                        ],
                                        "representation_policy_artifact": ".vero/representation_policies/ghost_view.json",
                                        "representation_policy_status": "draft_blocked_pending_human_decision",
                                    }
                                ],
                            }
                        ],
                    }
                ]
            },
            indent=2,
        )
    )

    result = check_policy_artifacts(dst)
    assert result.status == "pass", [f.message for f in result.details]


def test_policy_artifacts_rejects_draft_policy_that_clears_blocker(
    tmp_path: Path,
) -> None:
    """A draft/blocked policy artifact must not let the plan look promotion-clean."""
    import json as _json
    import shutil

    from vero.curation.validation.checks import check_policy_artifacts

    dst = tmp_path / "bench"
    shutil.copytree(REFERENCE, dst)
    vero = dst / ".vero"
    policy_dir = dst / ".vero" / "trusted_callback_policies"
    policy_dir.mkdir(parents=True)
    (vero / "source_index.json").write_text(
        _json.dumps(
            {
                "version": 1,
                "source_language": "verus",
                "generated_at": "2026-06-01T00:00:00Z",
                "entities": [
                    {
                        "id": "io.rs:send:10",
                        "name": "send",
                        "kind": "fn",
                        "source_file": "io.rs",
                        "source_line": 10,
                        "selected": True,
                    },
                    {
                        "id": "io.rs:extern_send:20",
                        "name": "extern_send",
                        "kind": "fn",
                        "source_file": "io.rs",
                        "source_line": 20,
                        "selected": True,
                    },
                ],
            },
            indent=2,
        )
    )
    (policy_dir / "send.json").write_text(
        _json.dumps(
            {
                "policy_id": "demo.send.v1",
                "status": "draft_blocked_pending_human_approval",
                "trusted_call_chain": [
                    {"name": "send", "source_id": "io.rs:send:10"},
                    {"name": "extern_send", "source_id": "io.rs:extern_send:20"},
                ],
                "trusted_assumptions": ["callback result is trusted"],
                "test_policy": {"current_status": "not_waived"},
                "promotion_effect": {
                    "may_clear_blocked_pending_trusted_callback_policy": False,
                    "may_waive_send_guard_warning": False,
                    "requires_human_approval": True,
                },
            },
            indent=2,
        )
    )
    (dst / ".vero" / "plan.json").write_text(
        _json.dumps(
            {
                "packages": [
                    {
                        "name": "BankLedger",
                        "modules": [
                            {
                                "name": "Io",
                                "apis": [
                                    {
                                        "name": "send",
                                        "promotion_scope": True,
                                        "promotion_status": "ready",
                                        "trusted_boundary_policy_artifact": ".vero/trusted_callback_policies/send.json",
                                        "trusted_boundary_policy_status": "draft_blocked_pending_human_approval",
                                    }
                                ],
                            }
                        ],
                    }
                ]
            },
            indent=2,
        )
    )

    result = check_policy_artifacts(dst)
    assert result.status == "fail"
    assert any("draft/blocked" in f.message for f in result.details)


def test_policy_artifacts_accepts_blocked_trusted_call_chain_source_ids(
    tmp_path: Path,
) -> None:
    """Blocked trusted-boundary policies still need exact source call chains."""
    import json as _json
    import shutil

    from vero.curation.validation.checks import check_policy_artifacts

    dst = tmp_path / "bench"
    shutil.copytree(REFERENCE, dst)
    vero = dst / ".vero"
    policy_dir = vero / "trusted_callback_policies"
    policy_dir.mkdir(parents=True)
    (vero / "source_index.json").write_text(
        _json.dumps(
            {
                "version": 1,
                "source_language": "verus",
                "generated_at": "2026-06-01T00:00:00Z",
                "entities": [
                    {
                        "id": "io.rs:send:10",
                        "name": "send",
                        "kind": "fn",
                        "source_file": "io.rs",
                        "source_line": 10,
                        "selected": True,
                    },
                    {
                        "id": "io.rs:send_internal_wrapper:20",
                        "name": "send_internal_wrapper",
                        "kind": "fn",
                        "source_file": "io.rs",
                        "source_line": 20,
                        "selected": True,
                        "semantic_disposition": "trusted_boundary_bridge_incomplete",
                    },
                ],
            },
            indent=2,
        )
    )
    (policy_dir / "send.json").write_text(
        _json.dumps(
            {
                "policy_id": "demo.send.v1",
                "status": "draft_blocked_pending_human_approval",
                "trusted_call_chain": [
                    {"name": "send", "source_id": "io.rs:send:10"},
                    {
                        "name": "send_internal_wrapper",
                        "source_id": "io.rs:send_internal_wrapper:20",
                    },
                ],
                "trusted_assumptions": ["external callback result is trusted"],
                "test_policy": {"current_status": "not_waived"},
                "promotion_effect": {
                    "may_clear_send_blocker": False,
                    "requires_human_approval": True,
                },
            },
            indent=2,
        )
    )
    (vero / "plan.json").write_text(
        _json.dumps(
            {
                "packages": [
                    {
                        "name": "BankLedger",
                        "modules": [
                            {
                                "name": "Io",
                                "apis": [
                                    {
                                        "name": "send",
                                        "promotion_status": "blocked_pending_trusted_callback_policy",
                                        "semantic_bridge_required": [
                                            "trusted callback policy"
                                        ],
                                        "trusted_boundary_policy_artifact": ".vero/trusted_callback_policies/send.json",
                                        "trusted_boundary_policy_status": "draft_blocked_pending_human_approval",
                                    }
                                ],
                            }
                        ],
                    }
                ]
            },
            indent=2,
        )
    )

    result = check_policy_artifacts(dst)
    assert result.status == "pass", [f.message for f in result.details]


def test_policy_artifacts_rejects_missing_trusted_call_chain_source_id(
    tmp_path: Path,
) -> None:
    """Trusted call-chain artifacts must not cite stale source ids."""
    import json as _json
    import shutil

    from vero.curation.validation.checks import check_policy_artifacts

    dst = tmp_path / "bench"
    shutil.copytree(REFERENCE, dst)
    vero = dst / ".vero"
    policy_dir = vero / "trusted_callback_policies"
    policy_dir.mkdir(parents=True)
    (vero / "source_index.json").write_text(
        _json.dumps(
            {
                "version": 1,
                "source_language": "verus",
                "generated_at": "2026-06-01T00:00:00Z",
                "entities": [],
            },
            indent=2,
        )
    )
    (policy_dir / "send.json").write_text(
        _json.dumps(
            {
                "policy_id": "demo.send.v1",
                "status": "draft_blocked_pending_human_approval",
                "trusted_call_chain": [{"name": "send", "source_id": "io.rs:send:10"}],
                "trusted_assumptions": ["external callback result is trusted"],
                "test_policy": {"current_status": "not_waived"},
                "promotion_effect": {
                    "may_clear_send_blocker": False,
                    "requires_human_approval": True,
                },
            },
            indent=2,
        )
    )
    (vero / "plan.json").write_text(
        _json.dumps(
            {
                "packages": [
                    {
                        "name": "BankLedger",
                        "modules": [
                            {
                                "name": "Io",
                                "apis": [
                                    {
                                        "name": "send",
                                        "promotion_status": "blocked_pending_trusted_callback_policy",
                                        "semantic_bridge_required": [
                                            "trusted callback policy"
                                        ],
                                        "trusted_boundary_policy_artifact": ".vero/trusted_callback_policies/send.json",
                                        "trusted_boundary_policy_status": "draft_blocked_pending_human_approval",
                                    }
                                ],
                            }
                        ],
                    }
                ]
            },
            indent=2,
        )
    )

    result = check_policy_artifacts(dst)
    assert result.status == "fail"
    assert any(
        "trusted_call_chain references missing source_index id" in f.message
        for f in result.details
    )


def test_policy_artifacts_rejects_status_mismatch(tmp_path: Path) -> None:
    """Plan metadata and the referenced artifact must agree on policy status."""
    import json as _json
    import shutil

    from vero.curation.validation.checks import check_policy_artifacts

    dst = tmp_path / "bench"
    shutil.copytree(REFERENCE, dst)
    policy_dir = dst / ".vero" / "macro_expansion_requirements"
    policy_dir.mkdir(parents=True)
    (policy_dir / "wire.json").write_text(
        _json.dumps(
            {
                "requirement_id": "demo.wire.v1",
                "status": "draft_blocked_pending_source_index_rule",
                "required_source_index_records": ["generated serializer"],
                "promotion_effect": {
                    "may_clear_wire_blocker": False,
                    "requires_source_index_rule": True,
                },
            },
            indent=2,
        )
    )
    (dst / ".vero" / "plan.json").write_text(
        _json.dumps(
            {
                "packages": [
                    {
                        "name": "BankLedger",
                        "modules": [
                            {
                                "name": "Wire",
                                "specs": [
                                    {
                                        "name": "spec_wire",
                                        "promotion_status": "blocked_pending_macro_rule",
                                        "macro_expansion_requirement_artifact": ".vero/macro_expansion_requirements/wire.json",
                                        "macro_expansion_requirement_status": "approved",
                                    }
                                ],
                            }
                        ],
                    }
                ]
            },
            indent=2,
        )
    )

    result = check_policy_artifacts(dst)
    assert result.status == "fail"
    assert any("does not match artifact status" in f.message for f in result.details)


def test_policy_artifacts_accepts_blocked_macro_trace_records(
    tmp_path: Path,
) -> None:
    """Blocked macro artifacts may cite bridge-incomplete trace records."""
    import json as _json
    import shutil

    from vero.curation.validation.checks import check_policy_artifacts

    dst = tmp_path / "bench"
    shutil.copytree(REFERENCE, dst)
    vero = dst / ".vero"
    macro_dir = vero / "macro_expansion_requirements"
    macro_dir.mkdir(parents=True)
    (vero / "source_index.json").write_text(
        _json.dumps(
            {
                "version": 1,
                "source_language": "verus",
                "generated_at": "2026-06-01T00:00:00Z",
                "entities": [
                    {
                        "id": "wire.rs:CSingleMessage.generated.deserialize:182",
                        "name": "CSingleMessage.generated.deserialize",
                        "kind": "macro_generated_fn",
                        "source_file": "wire.rs",
                        "source_line": 182,
                        "selected": True,
                        "semantic_disposition": "macro_expansion_bridge_incomplete",
                    }
                ],
            },
            indent=2,
        )
    )
    (macro_dir / "wire.json").write_text(
        _json.dumps(
            {
                "requirement_id": "demo.wire.v1",
                "status": "draft_blocked_pending_source_index_rule",
                "required_source_index_records": ["generated deserialize"],
                "available_source_index_trace_records": {
                    "CSingleMessage": [
                        "wire.rs:CSingleMessage.generated.deserialize:182"
                    ]
                },
                "promotion_effect": {
                    "may_clear_wire_blocker": False,
                    "requires_source_index_rule": True,
                },
            },
            indent=2,
        )
    )
    (vero / "plan.json").write_text(
        _json.dumps(
            {
                "packages": [
                    {
                        "name": "BankLedger",
                        "modules": [
                            {
                                "name": "Wire",
                                "specs": [
                                    {
                                        "name": "spec_wire",
                                        "promotion_status": "blocked_pending_macro_rule",
                                        "semantic_bridge_required": [
                                            "type-specific macro expansion bridge"
                                        ],
                                        "macro_expansion_requirement_artifact": ".vero/macro_expansion_requirements/wire.json",
                                        "macro_expansion_requirement_status": "draft_blocked_pending_source_index_rule",
                                    }
                                ],
                            }
                        ],
                    }
                ]
            },
            indent=2,
        )
    )

    result = check_policy_artifacts(dst)
    assert result.status == "pass", [f.message for f in result.details]


def test_policy_artifacts_rejects_missing_macro_trace_record(
    tmp_path: Path,
) -> None:
    """Artifact trace lists must not drift away from source_index.json."""
    import json as _json
    import shutil

    from vero.curation.validation.checks import check_policy_artifacts

    dst = tmp_path / "bench"
    shutil.copytree(REFERENCE, dst)
    vero = dst / ".vero"
    macro_dir = vero / "macro_expansion_requirements"
    macro_dir.mkdir(parents=True)
    (vero / "source_index.json").write_text(
        _json.dumps(
            {
                "version": 1,
                "source_language": "verus",
                "generated_at": "2026-06-01T00:00:00Z",
                "entities": [],
            },
            indent=2,
        )
    )
    (macro_dir / "wire.json").write_text(
        _json.dumps(
            {
                "requirement_id": "demo.wire.v1",
                "status": "draft_blocked_pending_source_index_rule",
                "required_source_index_records": ["generated deserialize"],
                "available_source_index_trace_records": {
                    "CSingleMessage": [
                        "wire.rs:CSingleMessage.generated.deserialize:182"
                    ]
                },
                "promotion_effect": {
                    "may_clear_wire_blocker": False,
                    "requires_source_index_rule": True,
                },
            },
            indent=2,
        )
    )
    (vero / "plan.json").write_text(
        _json.dumps(
            {
                "packages": [
                    {
                        "name": "BankLedger",
                        "modules": [
                            {
                                "name": "Wire",
                                "specs": [
                                    {
                                        "name": "spec_wire",
                                        "promotion_status": "blocked_pending_macro_rule",
                                        "semantic_bridge_required": [
                                            "type-specific macro expansion bridge"
                                        ],
                                        "macro_expansion_requirement_artifact": ".vero/macro_expansion_requirements/wire.json",
                                        "macro_expansion_requirement_status": "draft_blocked_pending_source_index_rule",
                                    }
                                ],
                            }
                        ],
                    }
                ]
            },
            indent=2,
        )
    )

    result = check_policy_artifacts(dst)
    assert result.status == "fail"
    assert any(
        "available_source_index_trace_records references missing source_index id"
        in f.message
        for f in result.details
    )


def test_policy_artifacts_rejects_clearance_with_blocked_dependency(
    tmp_path: Path,
) -> None:
    """A policy cannot clear while one of its policy dependencies is blocked."""
    import json as _json
    import shutil

    from vero.curation.validation.checks import check_policy_artifacts

    dst = tmp_path / "bench"
    shutil.copytree(REFERENCE, dst)
    policy_dir = dst / ".vero" / "representation_policies"
    policy_dir.mkdir(parents=True)
    (policy_dir / "delegation.json").write_text(
        _json.dumps(
            {
                "policy_id": "demo.delegation.v1",
                "status": "draft_blocked_pending_human_decision",
                "blocked_specs": ["spec_delegation"],
                "promotion_effect": {
                    "may_clear_delegation_blocker": False,
                    "requires_human_decision": True,
                },
            },
            indent=2,
        )
    )
    (policy_dir / "host.json").write_text(
        _json.dumps(
            {
                "policy_id": "demo.host.v1",
                "status": "approved",
                "blocked_specs": ["spec_host"],
                "depends_on": ["demo.delegation.v1"],
                "promotion_effect": {
                    "may_clear_host_blocker": True,
                    "requires_human_decision": False,
                },
            },
            indent=2,
        )
    )
    (dst / ".vero" / "plan.json").write_text(
        _json.dumps(
            {
                "packages": [
                    {
                        "name": "BankLedger",
                        "modules": [
                            {
                                "name": "Host",
                                "specs": [
                                    {
                                        "name": "spec_host",
                                        "promotion_scope": True,
                                        "promotion_status": "ready",
                                        "representation_policy_artifact": ".vero/representation_policies/host.json",
                                        "representation_policy_status": "approved",
                                    },
                                    {
                                        "name": "spec_delegation",
                                        "promotion_scope": True,
                                        "promotion_status": "blocked_pending_delegation_policy",
                                        "semantic_bridge_required": [
                                            "delegation ghost map bridge"
                                        ],
                                        "representation_policy_artifact": ".vero/representation_policies/delegation.json",
                                        "representation_policy_status": "draft_blocked_pending_human_decision",
                                    },
                                ],
                            }
                        ],
                    }
                ]
            },
            indent=2,
        )
    )

    result = check_policy_artifacts(dst)
    assert result.status == "fail"
    assert any("depends on blocked policy" in f.message for f in result.details)


def test_policy_artifacts_rejects_approved_macro_template_evidence(
    tmp_path: Path,
) -> None:
    """Approved macro requirements need type-specific generated evidence."""
    import json as _json
    import shutil

    from vero.curation.validation.checks import check_policy_artifacts

    dst = tmp_path / "bench"
    shutil.copytree(REFERENCE, dst)
    vero = dst / ".vero"
    macro_dir = vero / "macro_expansion_requirements"
    macro_dir.mkdir(parents=True)
    (vero / "source_index.json").write_text(
        _json.dumps(
            {
                "version": 1,
                "source_language": "verus",
                "generated_at": "2026-06-01T00:00:00Z",
                "entities": [
                    {
                        "id": "marshal_v.rs:enum_template:view_equal",
                        "name": "enum_template.view_equal",
                        "kind": "macro_generated_fn_template",
                        "source_file": "marshal_v.rs",
                        "source_line": 1394,
                        "selected": True,
                    }
                ],
            },
            indent=2,
        )
    )
    (macro_dir / "wire.json").write_text(
        _json.dumps(
            {
                "requirement_id": "demo.wire.v1",
                "status": "approved",
                "required_source_index_records": ["generated view_equal"],
                "source_index_evidence": [
                    {
                        "source_id": "marshal_v.rs:enum_template:view_equal",
                        "type_name": "CSingleMessage",
                        "generated_role": "view_equal",
                    }
                ],
                "promotion_effect": {
                    "may_clear_wire_blocker": True,
                    "requires_source_index_rule": False,
                },
            },
            indent=2,
        )
    )
    (vero / "plan.json").write_text(
        _json.dumps(
            {
                "packages": [
                    {
                        "name": "BankLedger",
                        "modules": [
                            {
                                "name": "Wire",
                                "specs": [
                                    {
                                        "name": "spec_wire",
                                        "promotion_scope": True,
                                        "promotion_status": "ready",
                                        "macro_expansion_requirement_artifact": ".vero/macro_expansion_requirements/wire.json",
                                        "macro_expansion_requirement_status": "approved",
                                    }
                                ],
                            }
                        ],
                    }
                ]
            },
            indent=2,
        )
    )

    result = check_policy_artifacts(dst)
    assert result.status == "fail"
    assert any("generic macro template" in f.message for f in result.details)


def test_policy_artifacts_rejects_incomplete_macro_evidence(tmp_path: Path) -> None:
    """Trace-only macro expansion records do not count as approved evidence."""
    import json as _json
    import shutil

    from vero.curation.validation.checks import check_policy_artifacts

    dst = tmp_path / "bench"
    shutil.copytree(REFERENCE, dst)
    vero = dst / ".vero"
    macro_dir = vero / "macro_expansion_requirements"
    macro_dir.mkdir(parents=True)
    (vero / "source_index.json").write_text(
        _json.dumps(
            {
                "version": 1,
                "source_language": "verus",
                "generated_at": "2026-06-01T00:00:00Z",
                "entities": [
                    {
                        "id": "cmessage_v.rs:CSingleMessage.macro:182",
                        "name": "CSingleMessage.macro",
                        "kind": "macro_expansion",
                        "source_file": "cmessage_v.rs",
                        "source_line": 182,
                        "selected": True,
                        "semantic_disposition": "macro_expansion_bridge_incomplete",
                    }
                ],
            },
            indent=2,
        )
    )
    (macro_dir / "wire.json").write_text(
        _json.dumps(
            {
                "requirement_id": "demo.wire.v1",
                "status": "approved",
                "required_source_index_records": ["generated deserialize"],
                "source_index_evidence": [
                    {
                        "source_id": "cmessage_v.rs:CSingleMessage.macro:182",
                        "type_name": "CSingleMessage",
                        "generated_role": "deserialize",
                    }
                ],
                "promotion_effect": {
                    "may_clear_wire_blocker": True,
                    "requires_source_index_rule": False,
                },
            },
            indent=2,
        )
    )
    (vero / "plan.json").write_text(
        _json.dumps(
            {
                "packages": [
                    {
                        "name": "BankLedger",
                        "modules": [
                            {
                                "name": "Wire",
                                "specs": [
                                    {
                                        "name": "spec_wire",
                                        "promotion_scope": True,
                                        "promotion_status": "ready",
                                        "macro_expansion_requirement_artifact": ".vero/macro_expansion_requirements/wire.json",
                                        "macro_expansion_requirement_status": "approved",
                                    }
                                ],
                            }
                        ],
                    }
                ]
            },
            indent=2,
        )
    )

    result = check_policy_artifacts(dst)
    assert result.status == "fail"
    assert any("not approved generated evidence" in f.message for f in result.details)


def test_plan_placeholder_bodies_rejects_plan_placeholder_helpers(
    tmp_path: Path,
) -> None:
    """Plan helpers/types must not freeze unknown semantics with fake bodies."""
    import json as _json
    import shutil

    from vero.curation.validation.checks import check_plan_placeholder_bodies

    dst = tmp_path / "bench"
    shutil.copytree(REFERENCE, dst)
    vero = dst / ".vero"
    vero.mkdir()
    (vero / "plan.json").write_text(
        _json.dumps(
            {
                "packages": [
                    {
                        "name": "BankLedger",
                        "modules": [
                            {
                                "name": "Account",
                                "types": [
                                    {
                                        "name": "BadState",
                                        "lean_form": "structure BadState where\n  m : Unit",
                                    }
                                ],
                                "api_helpers": [
                                    {
                                        "name": "fakeNone",
                                        "lean_form": "noncomputable def fakeNone : Option Nat := none",
                                    },
                                    {
                                        "name": "fakeFalse",
                                        "lean_form": "def fakeFalse : Bool := false",
                                    },
                                ],
                                "spec_helpers": [
                                    {
                                        "name": "fakeDefault",
                                        "lean_form": "noncomputable def fakeDefault : Nat := default",
                                    },
                                    {
                                        "name": "fakeEmptyList",
                                        "lean_form": "def fakeEmptyList : List Nat := []",
                                    },
                                    {
                                        "name": "fakeUnit",
                                        "lean_form": "def fakeUnit : Unit := ()",
                                    },
                                ],
                            }
                        ],
                    }
                ]
            },
            indent=2,
        )
    )

    result = check_plan_placeholder_bodies(dst)
    assert result.status == "fail"
    messages = [f.message for f in result.details]
    assert any("placeholder body" in m for m in messages)
    assert any("fakeFalse" in m for m in messages)
    assert any("fakeEmptyList" in m for m in messages)
    assert any("Unit := ()" in m for m in messages)
    assert any("erases model state" in m for m in messages)


def test_config_hygiene_rejects_local_codex_credentials(tmp_path: Path) -> None:
    """Local Codex curation configs must not persist API credentials."""
    import shutil

    from vero.curation.validation.checks import check_config_hygiene

    dst = tmp_path / "bench"
    shutil.copytree(REFERENCE, dst)
    (dst / "config.yaml").write_text(
        "\n".join(
            [
                "agent_kind: codex",
                "codex_auth_mode: local",
                "api_key: sk-test",
                "api_base_url: https://proxy.example",
            ]
        )
        + "\n",
        encoding="utf-8",
    )

    result = check_config_hygiene(dst)
    assert result.status == "fail"
    assert any("api_key=null" in f.message for f in result.details)
    assert any("api_base_url=null" in f.message for f in result.details)


def test_config_hygiene_accepts_local_codex_null_credentials(tmp_path: Path) -> None:
    """The VerifiedIronKV local-auth shape is valid when creds are redacted."""
    import shutil

    from vero.curation.validation.checks import check_config_hygiene

    dst = tmp_path / "bench"
    shutil.copytree(REFERENCE, dst)
    (dst / "config.yaml").write_text(
        "\n".join(
            [
                "agent_kind: codex",
                "codex_auth_mode: local",
                "api_key: null",
                "api_base_url: null",
            ]
        )
        + "\n",
        encoding="utf-8",
    )

    result = check_config_hygiene(dst)
    assert result.status == "pass", [f.message for f in result.details]


# ─── spec_shape: regression fixtures ────────────────────────────────


def test_spec_shape_rejects_theorem_in_spec_file(tmp_path: Path) -> None:
    """Copy reference, inject a theorem into Spec/Account.lean, expect fail."""
    import shutil

    from vero.curation.validation.checks import check_spec_shape

    dst = tmp_path / "bench"
    shutil.copytree(REFERENCE, dst)
    spec_file = dst / "BankLedger" / "Spec" / "Account.lean"
    spec_file.write_text(
        spec_file.read_text() + "\ntheorem bogus (impl : RepoImpl) : True := trivial\n"
    )
    result = check_spec_shape(dst)
    assert result.status == "fail"
    assert any("theorem" in f.message for f in result.details)


def test_spec_shape_rejects_wrong_spec_type(tmp_path: Path) -> None:
    """A listed spec must be `(impl : RepoImpl) : Prop`."""
    import json as _json
    import shutil

    from vero.curation.validation.checks import check_spec_shape

    dst = tmp_path / "bench"
    shutil.copytree(REFERENCE, dst)
    manifest = _json.loads((dst / "manifest.json").read_text())
    # Add a listed spec whose def in the spec file is wrongly typed
    manifest["packages"][0]["modules"][0]["specs"].append("spec_wrong_shape")
    (dst / "manifest.json").write_text(_json.dumps(manifest, indent=2))
    spec_file = dst / "BankLedger" / "Spec" / "Account.lean"
    spec_file.write_text(
        spec_file.read_text() + "\ndef spec_wrong_shape (n : Nat) : Nat := n\n"
    )
    result = check_spec_shape(dst)
    assert result.status == "fail"
    assert any("spec_wrong_shape" in f.message for f in result.details)


def test_spec_shape_rejects_unmanifested_spec_defs(tmp_path: Path) -> None:
    """A `def spec_*` in Spec/ must be listed in manifest specs or spec_helpers."""
    import shutil

    from vero.curation.validation.checks import check_spec_shape

    dst = tmp_path / "bench"
    shutil.copytree(REFERENCE, dst)
    spec_file = dst / "BankLedger" / "Spec" / "Account.lean"
    spec_file.write_text(
        spec_file.read_text() + "\ndef spec_helper_foo (n : Nat) : Bool := n == 0\n"
    )
    result = check_spec_shape(dst)
    assert result.status == "fail"
    assert any("spec_helper_foo" in f.message for f in result.details)


def test_spec_shape_allows_explicit_spec_helpers(tmp_path: Path) -> None:
    """Explicit `spec_helpers` are allowed but must be intentional in the manifest."""
    import json as _json
    import shutil

    from vero.curation.validation.checks import check_spec_shape

    dst = tmp_path / "bench"
    shutil.copytree(REFERENCE, dst)
    manifest = _json.loads((dst / "manifest.json").read_text())
    manifest["packages"][0]["modules"][0].setdefault("spec_helpers", []).append(
        {"name": "spec_helper_foo"}
    )
    (dst / "manifest.json").write_text(_json.dumps(manifest, indent=2))
    spec_file = dst / "BankLedger" / "Spec" / "Account.lean"
    spec_file.write_text(
        spec_file.read_text()
        + "\ndef spec_helper_foo (impl : RepoImpl) : Prop := True\n"
    )
    result = check_spec_shape(dst)
    assert result.status == "pass"


def test_spec_quality_warns_on_vacuous_true_spec(tmp_path: Path) -> None:
    """A manifest-listed spec ending in True should be surfaced as likely vacuous."""
    import json as _json
    import shutil

    from vero.curation.validation.checks import check_spec_quality

    dst = tmp_path / "bench"
    shutil.copytree(REFERENCE, dst)
    manifest = _json.loads((dst / "manifest.json").read_text())
    manifest["packages"][0]["modules"][0]["specs"].append("spec_placeholder")
    (dst / "manifest.json").write_text(_json.dumps(manifest, indent=2))
    spec_file = dst / "BankLedger" / "Spec" / "Account.lean"
    spec_file.write_text(
        spec_file.read_text()
        + "\ndef spec_placeholder (_impl : RepoImpl) : Prop :=\n"
        + "  forall (id : AccountId), id = id -> True\n"
    )
    result = check_spec_quality(dst)
    assert result.status == "warn"
    assert any("spec_placeholder" in f.message for f in result.details)


def test_api_spec_coverage_warns_when_api_unmentioned(tmp_path: Path) -> None:
    """A public API with no reference from Spec files should be a quality warning."""
    import json as _json
    import shutil

    from vero.curation.validation.checks import check_api_spec_coverage

    dst = tmp_path / "bench"
    shutil.copytree(REFERENCE, dst)
    manifest = _json.loads((dst / "manifest.json").read_text())
    manifest["packages"][0]["modules"][0]["apis"].append(
        {"name": "unusedApi", "sig": "UnusedApiSig", "type": "Ledger -> Ledger"}
    )
    (dst / "manifest.json").write_text(_json.dumps(manifest, indent=2))
    result = check_api_spec_coverage(dst)
    assert result.status == "warn"
    assert any("unusedApi" in f.message for f in result.details)


def test_provenance_warns_for_translated_without_source_map(tmp_path: Path) -> None:
    """Translated benchmarks should carry validator-readable source provenance."""
    import json as _json
    import shutil

    from vero.curation.validation.checks import check_provenance

    dst = tmp_path / "bench"
    shutil.copytree(REFERENCE, dst)
    manifest = _json.loads((dst / "manifest.json").read_text())
    manifest["source"] = {
        "kind": "translated",
        "language": "coq",
        "repo_url": "https://example.invalid/repo",
        "commit_hash": "abc123",
        "path": "src",
    }
    (dst / "manifest.json").write_text(_json.dumps(manifest, indent=2))
    result = check_provenance(dst)
    assert result.status == "warn"
    assert any("source provenance artifact" in f.message for f in result.details)


def test_provenance_passes_with_source_map(tmp_path: Path) -> None:
    """A translated benchmark with a source map should satisfy provenance."""
    import json as _json
    import shutil

    from vero.curation.validation.checks import check_provenance

    dst = tmp_path / "bench"
    shutil.copytree(REFERENCE, dst)
    manifest = _json.loads((dst / "manifest.json").read_text())
    manifest["source"] = {
        "kind": "translated",
        "language": "coq",
        "repo_url": "https://example.invalid/repo",
        "commit_hash": "abc123",
        "path": "src",
    }
    (dst / "manifest.json").write_text(_json.dumps(manifest, indent=2))
    vero = dst / ".vero"
    vero.mkdir()
    (vero / "source_map.json").write_text("{}")
    result = check_provenance(dst)
    assert result.status == "pass"


def test_trusted_boundary_warns_on_benchmark_specific_trusted_name(
    tmp_path: Path,
) -> None:
    """Trusted names with benchmark-specific terms need explicit boundary review."""
    import json as _json
    import shutil

    from vero.curation.validation.checks import check_trusted_boundary

    dst = tmp_path / "bench"
    shutil.copytree(REFERENCE, dst)
    manifest = _json.loads((dst / "manifest.json").read_text())
    manifest["trusted_axioms"] = ["PiggyBank.owner_magic"]
    (dst / "manifest.json").write_text(_json.dumps(manifest, indent=2))
    result = check_trusted_boundary(dst)
    assert result.status == "warn"
    assert any("benchmark-specific" in f.message for f in result.details)


# ─── manifest_vs_code: api_helper kind recognition ──────────────────


def test_manifest_api_helper_kind_skips_sig_requirement(tmp_path: Path) -> None:
    """api_helper kind does not require a sig abbrev; the fn def must still exist."""
    import json as _json
    import shutil

    from vero.curation.validation.checks import check_manifest_vs_code

    dst = tmp_path / "bench"
    shutil.copytree(REFERENCE, dst)
    manifest = _json.loads((dst / "manifest.json").read_text())
    # Add an api_helper that exists in Impl/Account.lean (createAccount is already there;
    # we pretend it's a helper for this fixture).
    manifest["packages"][0]["modules"][0]["apis"].append(
        {"name": "closeAccount", "kind": "api_helper"}
    )
    # Remove it from the original apis[] first to avoid duplicate sig requirement.
    manifest["packages"][0]["modules"][0]["apis"] = [
        a
        for a in manifest["packages"][0]["modules"][0]["apis"]
        if a.get("name") != "closeAccount" or a.get("kind") == "api_helper"
    ]
    (dst / "manifest.json").write_text(_json.dumps(manifest, indent=2))
    result = check_manifest_vs_code(dst)
    # Should still pass: closeAccount as helper doesn't need its sig abbrev ref
    errors = [f for f in result.details if f.severity == "error"]
    assert not errors, [f.message for f in errors]


# ─── Marker parser unit tests ───────────────────────────────────────


def test_parse_marker_line_benchmark() -> None:
    m = parse_marker_line(
        "-- !benchmark @start proof def=prove_S kind=prove target=spec_S", 42
    )
    assert m is not None
    assert m.prefix == "benchmark"
    assert m.boundary == "start"
    assert m.key == "proof"
    assert m.fields == {"def": "prove_S", "kind": "prove", "target": "spec_S"}
    assert m.line_no == 42


def test_parse_marker_line_solution() -> None:
    m = parse_marker_line(
        "-- !solution @start def=joint_unsatisfiability kind=joint_unsat", 1
    )
    assert m is not None
    assert m.prefix == "solution"
    assert m.boundary == "start"
    assert m.fields == {"def": "joint_unsatisfiability", "kind": "joint_unsat"}


def test_parse_marker_line_curation() -> None:
    m = parse_marker_line(
        "-- !curation @review v1 [ ] createAccount — Impl/Account, code, sorry",
        10,
    )
    assert m is not None
    assert m.prefix == "curation"
    assert m.curation_kind == "review"
    assert m.curation_body is not None


def test_parse_marker_line_non_marker() -> None:
    assert parse_marker_line("-- just a comment", 1) is None
    assert parse_marker_line("import BankLedger.Harness", 1) is None


def test_pair_slots_balance() -> None:
    markers = [
        parse_marker_line("-- !benchmark @start imports", 1),
        parse_marker_line("-- !benchmark @end imports", 2),
        parse_marker_line("-- !benchmark @start code def=foo", 3),
        parse_marker_line("-- !benchmark @end code def=foo", 4),
    ]
    markers = [m for m in markers if m is not None]
    pairs, errors = pair_slots(markers)
    assert not errors
    assert len(pairs) == 2


def test_pair_slots_mismatch() -> None:
    markers = [
        parse_marker_line("-- !benchmark @start code def=foo", 1),
        parse_marker_line("-- !benchmark @end code def=bar", 2),
    ]
    markers = [m for m in markers if m is not None]
    _, errors = pair_slots(markers)
    assert errors
    assert any("def mismatch" in e for e in errors)


def test_parse_file_markers_on_reference_harness() -> None:
    """Harness must be marker-free per file-role constraint."""
    markers = parse_file_markers(REFERENCE / "BankLedger" / "Harness.lean")
    assert markers == []


def test_parse_file_markers_on_reference_impl() -> None:
    markers = parse_file_markers(REFERENCE / "BankLedger" / "Impl" / "Account.lean")
    assert markers, "Impl/Account should have markers"
    # Expect imports + global_aux + 4 APIs × (code_aux + code) = 2 + 8 = 10 pairs = 20 marker lines
    keys = [m.key for m in markers if m.prefix == "benchmark"]
    assert "imports" in keys
    assert "global_aux" in keys
    assert keys.count("code") == 8  # 4 starts + 4 ends
    assert keys.count("code_aux") == 8


def test_benchmark_keys_set() -> None:
    assert BENCHMARK_KEYS == {
        "imports",
        "global_aux",
        "code",
        "code_aux",
        "proof",
        "proof_aux",
        "claim",
    }


# ─── Report serialization ───────────────────────────────────────────


def test_report_to_dict_shape() -> None:
    report = validate_benchmark(REFERENCE, skip_build=True)
    d = report.to_dict()
    assert d["version"] == 1
    assert d["overall"] in {"pass", "warn", "fail"}
    assert isinstance(d["blockers"], list)
    assert "manifest_schema" in d["rule_checks"]


# ─── Optional: build check (slow, skipped by default in CI) ─────────


@pytest.mark.slow
def test_reference_build_pass() -> None:
    """Full `lake build` against the reference. Slow — opt in with `-m slow`."""
    report = validate_benchmark(REFERENCE, skip_build=False, build_timeout=180)
    assert report.rule_checks["build"].status in {"pass", "warn"}
