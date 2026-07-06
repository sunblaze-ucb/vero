"""Integration test for the InitStage manifest scaffold."""

from __future__ import annotations

import asyncio
import json
from pathlib import Path

from vero.curation.config import CurationConfig
from vero.curation.models import SourceLanguage
from vero.curation.stages.base import StageContext
from vero.curation.stages.init import InitStage, _manifest_scaffold


def test_manifest_scaffold_shape() -> None:
    m = _manifest_scaffold(
        benchmark_id="bank_ledger",
        project_name="BankLedger",
        lean_version="4.29.1",
        source_language="verus",
        repo_url="https://example.com/repo",
        commit_hash="abc123",
        source_subdir="src",
    )
    assert m["benchmark_id"] == "bank_ledger"
    assert m["lean_version"] == "4.29.1"
    assert m["modes_supported"] == ["proof", "codeproof"]
    assert m["source"] == {
        "kind": "translated",
        "language": "verus",
        "repo_url": "https://example.com/repo",
        "commit_hash": "abc123",
        "path": "src",
    }
    assert m["root_package"] == "BankLedger"
    assert m["files"] == {
        "root_hub": "BankLedger.lean",
        "harness": "BankLedger/Harness.lean",
        "test": "BankLedger/Test.lean",
        "lakefile": "lakefile.toml",
    }
    assert m["packages"] == []


def test_manifest_scaffold_hand_crafted_nulls() -> None:
    m = _manifest_scaffold(
        benchmark_id="x",
        project_name="X",
        lean_version="4.29.1",
        source_language=None,
        repo_url="",
        commit_hash="",
        source_subdir="",
    )
    assert m["source"]["kind"] == "hand-crafted"
    assert m["source"]["language"] is None
    assert m["source"]["repo_url"] is None
    assert m["source"]["commit_hash"] is None
    assert m["source"]["path"] is None


def test_init_stage_writes_scaffold(tmp_path: Path) -> None:
    """Running InitStage against a minimal Dafny source produces the scaffold."""
    source_dir = tmp_path / "src"
    source_dir.mkdir()
    # Minimal Dafny file so detect_language finds something.
    (source_dir / "hello.dfy").write_text("method Main() {}\n")

    output_dir = tmp_path / "out"

    config = CurationConfig(
        source_dir=str(source_dir),
        output_dir=str(output_dir),
        benchmark_id="hello_bench",
    )
    # save() under the workspace so InitStage can reload
    output_dir.mkdir()
    config.save()
    ctx = StageContext.from_config(config)

    result = asyncio.run(InitStage().run(ctx))
    assert result.success, result.error

    project_dir = config.lean_output_dir / "HelloBench"
    assert (project_dir / "lakefile.toml").exists()
    assert (
        project_dir / "lean-toolchain"
    ).read_text().strip() == "leanprover/lean4:v4.29.1"
    assert (project_dir / "HelloBench.lean").exists()

    manifest = json.loads((project_dir / "manifest.json").read_text())
    assert manifest["benchmark_id"] == "hello_bench"
    assert manifest["root_package"] == "HelloBench"
    assert manifest["source"]["language"] == SourceLanguage.DAFNY.value
    assert manifest["packages"] == []


def test_init_stage_lakefile_new_form(tmp_path: Path) -> None:
    source_dir = tmp_path / "src"
    source_dir.mkdir()
    (source_dir / "a.dfy").write_text("")
    output_dir = tmp_path / "out"
    output_dir.mkdir()
    config = CurationConfig(
        source_dir=str(source_dir),
        output_dir=str(output_dir),
        benchmark_id="x",
    )
    config.save()
    ctx = StageContext.from_config(config)
    asyncio.run(InitStage().run(ctx))

    lakefile = (config.lean_output_dir / "X" / "lakefile.toml").read_text()
    assert "[package]" not in lakefile, "lakefile should use new top-level-fields form"
    assert 'defaultTargets = ["X"]' in lakefile
    assert 'srcDir = "."' in lakefile
