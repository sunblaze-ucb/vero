"""Integration test for the ValidateStage."""

from __future__ import annotations

import asyncio
import json
from dataclasses import dataclass
from pathlib import Path

import pytest

from vero.curation.config import CurationConfig
from vero.curation.stages.validate import (
    ValidateStage,
    find_benchmark_root,
    render_report_md,
)
from vero.curation.validation import validate_benchmark
from vero.curation.validation.llm_runner import CODEX_LLM_REVIEW_MODEL
from vero.curation.validation.types import CheckResult, Finding

REPO_ROOT = Path(__file__).parent.parent.parent
REFERENCE = REPO_ROOT / "reference"  # parent of BankLedger/
BANKLEDGER = REFERENCE / "BankLedger"


@dataclass
class _FakeCtx:
    """Minimal StageContext stand-in — only the fields ValidateStage uses."""

    curation_dir: Path
    lean_output_dir: Path
    config: CurationConfig | None = None


def test_find_benchmark_root_detects_sibling() -> None:
    """Given `reference/`, discovers `reference/BankLedger/` by manifest presence."""
    found = find_benchmark_root(REFERENCE)
    assert found is not None
    assert (found / "manifest.json").exists()
    assert found.name == "BankLedger"


def test_find_benchmark_root_direct() -> None:
    """Called on the Lean project directly, returns it unchanged."""
    found = find_benchmark_root(BANKLEDGER)
    assert found == BANKLEDGER


def test_find_benchmark_root_none(tmp_path: Path) -> None:
    assert find_benchmark_root(tmp_path) is None
    assert find_benchmark_root(tmp_path / "does-not-exist") is None


def test_find_benchmark_root_prefers_expected_project(tmp_path: Path) -> None:
    """Expected project names prevent stale sibling roots from winning by sort order."""
    lean_output = tmp_path / "lean_output"
    (lean_output / "Ironsht").mkdir(parents=True)
    (lean_output / "VerifiedIronkv").mkdir()
    (lean_output / "Ironsht" / "manifest.json").write_text("{}")
    (lean_output / "VerifiedIronkv" / "manifest.json").write_text("{}")

    assert find_benchmark_root(lean_output, "VerifiedIronkv") == (
        lean_output / "VerifiedIronkv"
    )
    assert find_benchmark_root(lean_output, "MissingProject") is None
    assert find_benchmark_root(lean_output) is None


def test_render_report_md_contains_sections() -> None:
    report = validate_benchmark(BANKLEDGER, skip_build=True)
    md = render_report_md(report)
    assert "Validation report" in md
    assert "Overall:" in md
    assert "manifest_schema" in md
    assert "markers_grammar" in md


def test_validate_stage_success_on_reference(tmp_path: Path) -> None:
    """Running ValidateStage against the reference benchmark should succeed."""
    ctx = _FakeCtx(curation_dir=tmp_path, lean_output_dir=REFERENCE)
    result = asyncio.run(ValidateStage().run(ctx))  # type: ignore[arg-type]

    assert result.success, f"stage failed: {result.error}"
    assert result.stage == "validate"
    assert len(result.output_files) == 2

    json_path = tmp_path / "validate.json"
    md_path = tmp_path / "validate" / "report.md"
    assert json_path.exists()
    assert md_path.exists()

    data = json.loads(json_path.read_text())
    assert data["version"] == 1
    assert data["overall"] in {"pass", "warn"}
    assert "rule_checks" in data


def test_validate_stage_llm_review_opt_in(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Opt-in LLM review is merged into validate outputs and memory candidates."""

    class FakeRunner:
        def __init__(self, **kwargs: object) -> None:
            self.kwargs = kwargs

    checks_file = tmp_path / "checks.yaml"
    checks_file.write_text("checks: []\n", encoding="utf-8")

    async def fake_run_llm_reviews_async(*args: object, **kwargs: object) -> dict:
        assert kwargs["only"] == ("repo_issue_taxonomy",)
        assert kwargs["check_specs_path"] == checks_file
        assert kwargs["runner"].kwargs["max_turns"] == 3
        assert kwargs["runner"].kwargs["model"] == CODEX_LLM_REVIEW_MODEL
        assert kwargs["runner"].kwargs["codex_auth_mode"] == "local"
        assert kwargs["runner"].kwargs["codex_sandbox_mode"] == "workspace-write"
        assert kwargs["runner"].kwargs["codex_network_access"] is True
        assert kwargs["runner"].kwargs["codex_timeout_seconds"] == 456
        assert kwargs["runner"].kwargs["codex_model_reasoning_effort"] == "high"
        return {
            "repo_issue_taxonomy": CheckResult(
                "repo_issue_taxonomy",
                "warn",
                [
                    Finding(
                        "warn",
                        "Tests mention constants but miss API behavior.",
                        "BankLedger/Test.lean:1",
                    )
                ],
            )
        }

    monkeypatch.setattr(
        "vero.curation.stages.validate.CurationAgentLLMReviewRunner",
        FakeRunner,
    )
    monkeypatch.setattr(
        "vero.curation.stages.validate.run_llm_reviews_async",
        fake_run_llm_reviews_async,
    )
    cfg = CurationConfig(
        source_dir=str(tmp_path),
        output_dir=str(tmp_path / "out"),
        validate_llm_review=True,
        validate_llm_review_checks=["repo_issue_taxonomy"],
        validate_llm_review_checks_path=str(checks_file),
        max_turns_validate=3,
        agent_kind="claude",
        model="claude-sonnet-4-6",
        codex_auth_mode="local",
        codex_sandbox_mode="workspace-write",
        codex_network_access=True,
        codex_timeout_seconds=456,
        codex_model_reasoning_effort="high",
    )
    ctx = _FakeCtx(curation_dir=tmp_path, lean_output_dir=REFERENCE, config=cfg)
    result = asyncio.run(ValidateStage().run(ctx))  # type: ignore[arg-type]

    assert result.success
    data = json.loads((tmp_path / "validate.json").read_text())
    assert data["llm_review"]["repo_issue_taxonomy"]["status"] == "warn"
    memory = (tmp_path / "validate" / "memory_candidates.md").read_text()
    assert "Tests mention constants" in memory


def test_validate_stage_failure_when_no_benchmark(tmp_path: Path) -> None:
    ctx = _FakeCtx(
        curation_dir=tmp_path / "curation", lean_output_dir=tmp_path / "empty"
    )
    (tmp_path / "empty").mkdir()
    result = asyncio.run(ValidateStage().run(ctx))  # type: ignore[arg-type]
    assert not result.success
    assert "No benchmark with manifest.json found" in result.error


@pytest.mark.slow
def test_validate_stage_with_build(tmp_path: Path) -> None:
    """End-to-end including `lake build`. Slow."""
    ctx = _FakeCtx(curation_dir=tmp_path, lean_output_dir=REFERENCE)
    result = asyncio.run(ValidateStage().run(ctx))  # type: ignore[arg-type]
    assert result.success
    data = json.loads((tmp_path / "validate.json").read_text())
    assert "build" in data["rule_checks"]
