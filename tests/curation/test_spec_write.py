"""Tests for the two-substep spec_write stage."""

from __future__ import annotations

import asyncio
import json
from pathlib import Path

import pytest

from vero.curation.stages.spec_write import (
    SpecWriteStage,
    _load_manifest_summary,
    determine_substep,
    is_plan_approved,
)

# ─── Approval gate ──────────────────────────────────────────────────


def test_approval_missing_plan(tmp_path: Path) -> None:
    plan = tmp_path / "spec_plan.md"
    assert is_plan_approved(plan) is False
    assert determine_substep(plan) == "reason"


def test_approval_unapproved_plan(tmp_path: Path) -> None:
    plan = tmp_path / "spec_plan.md"
    plan.write_text("# Spec proposals\n\nsome content\n", encoding="utf-8")
    assert is_plan_approved(plan) is False
    assert determine_substep(plan) == "reason"


def test_approval_approved_plan(tmp_path: Path) -> None:
    plan = tmp_path / "spec_plan.md"
    plan.write_text("# APPROVED\n\nproposals follow\n\n## spec_foo\n", encoding="utf-8")
    assert is_plan_approved(plan) is True
    assert determine_substep(plan) == "formalize"


def test_approval_marker_must_be_near_top(tmp_path: Path) -> None:
    """A `# APPROVED` deep in the file (e.g. quoted in a notes section) must NOT release the gate."""
    plan = tmp_path / "spec_plan.md"
    body = ["# Spec proposals", ""]
    body.extend(["filler line"] * 20)
    body.append("# APPROVED")  # too deep — line 23
    plan.write_text("\n".join(body), encoding="utf-8")
    assert is_plan_approved(plan) is False


def test_approval_with_leading_blank_lines(tmp_path: Path) -> None:
    plan = tmp_path / "spec_plan.md"
    plan.write_text("\n\n# APPROVED\n\nbody\n", encoding="utf-8")
    assert is_plan_approved(plan) is True


# ─── Manifest digest ────────────────────────────────────────────────


def _write_manifest(dir_: Path, *, modules: list[dict]) -> None:
    manifest = {
        "benchmark_id": "bench_x",
        "lean_version": "4.29.1",
        "modes_supported": ["proof"],
        "source": {},
        "curation": {},
        "files": {
            "root_hub": "BenchX.lean",
            "harness": "BenchX/Harness.lean",
            "test": "BenchX/Test.lean",
            "lakefile": "lakefile.toml",
        },
        "root_package": "BenchX",
        "packages": [
            {
                "name": "BenchX",
                "bundle": "BenchX/Bundle.lean",
                "bundle_type": "BenchXBundle",
                "repo_impl_field": "benchX",
                "modules": modules,
            }
        ],
    }
    (dir_ / "manifest.json").write_text(json.dumps(manifest), encoding="utf-8")


def test_manifest_summary_lists_apis_and_specs(tmp_path: Path) -> None:
    _write_manifest(
        tmp_path,
        modules=[
            {
                "name": "Account",
                "impl": "BenchX/Impl/Account.lean",
                "spec": "BenchX/Spec/Account.lean",
                "apis": [
                    {"name": "createAccount", "sig": "Sig", "type": "T", "kind": "api"},
                    {"name": "closeAccount", "sig": "Sig", "type": "T"},
                ],
                "specs": ["spec_create_zero_balance"],
            },
        ],
    )
    summary = _load_manifest_summary(tmp_path)
    assert summary["benchmark_id"] == "bench_x"
    assert len(summary["modules"]) == 1
    mod = summary["modules"][0]
    assert mod["name"] == "Account"
    assert mod["apis"] == ["createAccount", "closeAccount"]
    assert mod["existing_specs"] == ["spec_create_zero_balance"]


def test_manifest_summary_handles_dict_form_specs(tmp_path: Path) -> None:
    _write_manifest(
        tmp_path,
        modules=[
            {
                "name": "M",
                "impl": "BenchX/Impl/M.lean",
                "spec": "BenchX/Spec/M.lean",
                "apis": [],
                "specs": [
                    "spec_str",
                    {"name": "spec_dict", "kind": "spec"},
                ],
            },
        ],
    )
    summary = _load_manifest_summary(tmp_path)
    assert summary["modules"][0]["existing_specs"] == ["spec_str", "spec_dict"]


def test_manifest_summary_missing_file(tmp_path: Path) -> None:
    summary = _load_manifest_summary(tmp_path)
    assert "error" in summary


def test_manifest_summary_invalid_json(tmp_path: Path) -> None:
    (tmp_path / "manifest.json").write_text("{not json", encoding="utf-8")
    summary = _load_manifest_summary(tmp_path)
    assert "error" in summary


# ─── Stage substep dispatch (smoke; agent calls mocked) ─────────────


def test_stage_fails_when_project_dir_missing(tmp_path: Path) -> None:
    """If the translate stage hasn't run, spec_write must error immediately."""
    from vero.curation.config import CurationConfig
    from vero.curation.models import SourceLanguage
    from vero.curation.stages.base import StageContext

    cfg = CurationConfig(
        benchmark_id="missing_project",
        source_language=SourceLanguage.DAFNY,
        source_dir=str(tmp_path / "src"),
        output_dir=str(tmp_path),
    )
    ctx = StageContext.from_config(cfg)
    stage = SpecWriteStage()
    result = asyncio.run(stage.run(ctx))
    assert result.success is False
    assert "Lean project not found" in result.error


def test_stage_routes_to_reason_when_plan_absent(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """With no spec_plan.md present, the stage should call _run_substep_reason."""
    from vero.curation.config import CurationConfig
    from vero.curation.models import SourceLanguage
    from vero.curation.stages.base import StageContext, StageResult

    cfg = CurationConfig(
        benchmark_id="bench",
        source_language=SourceLanguage.DAFNY,
        source_dir=str(tmp_path / "src"),
        output_dir=str(tmp_path),
    )
    project_dir = cfg.lean_output_dir / "Bench"
    project_dir.mkdir(parents=True)
    cfg.curation_dir.mkdir()
    ctx = StageContext.from_config(cfg)

    called: dict[str, str] = {}

    async def fake_reason(self, ctx, project_dir, plan_path):  # noqa: ARG001
        called["substep"] = "reason"
        return StageResult(stage="spec_write", success=True)

    async def fake_formalize(self, ctx, project_dir, plan_path):  # noqa: ARG001
        called["substep"] = "formalize"
        return StageResult(stage="spec_write", success=True)

    monkeypatch.setattr(SpecWriteStage, "_run_substep_reason", fake_reason)
    monkeypatch.setattr(SpecWriteStage, "_run_substep_formalize", fake_formalize)

    stage = SpecWriteStage()
    result = asyncio.run(stage.run(ctx))
    assert result.success is True
    assert called == {"substep": "reason"}


def test_stage_routes_to_formalize_when_plan_approved(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    from vero.curation.config import CurationConfig
    from vero.curation.models import SourceLanguage
    from vero.curation.stages.base import StageContext, StageResult

    cfg = CurationConfig(
        benchmark_id="bench",
        source_language=SourceLanguage.DAFNY,
        source_dir=str(tmp_path / "src"),
        output_dir=str(tmp_path),
    )
    project_dir = cfg.lean_output_dir / "Bench"
    project_dir.mkdir(parents=True)
    cfg.curation_dir.mkdir()
    (cfg.curation_dir / "spec_plan.md").write_text(
        "# APPROVED\n\nbody\n", encoding="utf-8"
    )
    ctx = StageContext.from_config(cfg)

    called: dict[str, str] = {}

    async def fake_reason(self, ctx, project_dir, plan_path):  # noqa: ARG001
        called["substep"] = "reason"
        return StageResult(stage="spec_write", success=True)

    async def fake_formalize(self, ctx, project_dir, plan_path):  # noqa: ARG001
        called["substep"] = "formalize"
        return StageResult(stage="spec_write", success=True)

    monkeypatch.setattr(SpecWriteStage, "_run_substep_reason", fake_reason)
    monkeypatch.setattr(SpecWriteStage, "_run_substep_formalize", fake_formalize)

    stage = SpecWriteStage()
    result = asyncio.run(stage.run(ctx))
    assert result.success is True
    assert called == {"substep": "formalize"}


# ─── Reason prompt content ──────────────────────────────────────────


def test_reason_prompt_includes_manifest_digest(tmp_path: Path) -> None:
    from vero.curation.config import CurationConfig
    from vero.curation.models import SourceLanguage
    from vero.curation.stages.base import StageContext

    cfg = CurationConfig(
        benchmark_id="bench",
        source_language=SourceLanguage.DAFNY,
        source_dir=str(tmp_path / "src"),
        output_dir=str(tmp_path),
    )
    project_dir = cfg.lean_output_dir / "Bench"
    project_dir.mkdir(parents=True)
    cfg.curation_dir.mkdir()
    _write_manifest(
        project_dir,
        modules=[
            {
                "name": "M",
                "impl": "Bench/Impl/M.lean",
                "spec": "Bench/Spec/M.lean",
                "apis": [{"name": "f", "sig": "S", "type": "T", "kind": "api"}],
                "specs": [],
            },
        ],
    )
    ctx = StageContext.from_config(cfg)
    stage = SpecWriteStage()
    plan_path = cfg.curation_dir / "spec_plan.md"
    prompt = stage._build_reason_prompt(ctx, project_dir, plan_path)
    assert "spec_plan.md" in prompt
    assert "REASON" in prompt
    assert '"f"' in prompt or "'f'" in prompt  # api name surfaces in JSON digest
    assert "vero-spec-write" in prompt


def test_formalize_prompt_quotes_approved_plan(tmp_path: Path) -> None:
    from vero.curation.config import CurationConfig
    from vero.curation.models import SourceLanguage
    from vero.curation.stages.base import StageContext

    cfg = CurationConfig(
        benchmark_id="bench",
        source_language=SourceLanguage.DAFNY,
        source_dir=str(tmp_path / "src"),
        output_dir=str(tmp_path),
    )
    project_dir = cfg.lean_output_dir / "Bench"
    project_dir.mkdir(parents=True)
    cfg.curation_dir.mkdir()
    plan_path = cfg.curation_dir / "spec_plan.md"
    plan_path.write_text(
        "# APPROVED\n\n## spec_foo\nNL: foo holds.\n", encoding="utf-8"
    )
    ctx = StageContext.from_config(cfg)
    stage = SpecWriteStage()
    prompt = stage._build_formalize_prompt(ctx, project_dir, plan_path)
    assert "FORMALIZE" in prompt
    assert "spec_foo" in prompt
    assert "(impl : RepoImpl) : Prop" in prompt
