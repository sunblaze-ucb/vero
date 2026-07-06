"""Tests for PythonAdjustBodiesStage (mode-A phase 2 — fill Impl bodies)."""

from __future__ import annotations

import asyncio
import json
from pathlib import Path

import pytest

from vero.curation.config import CurationConfig
from vero.curation.models import SourceLanguage
from vero.curation.stages.base import StageContext
from vero.curation.stages.python_adjust_bodies import (
    PythonAdjustBodiesStage,
    _resolve_python_source_dir,
    count_unfilled_code_bodies,
)

# ─── Helpers ─────────────────────────────────────────────────────────


def _make_scaffold(
    output_dir: Path,
    *,
    benchmark_id: str,
    impl_bodies: dict[str, str],  # api_name -> body inside the marker
) -> Path:
    """Materialize a minimal mode-A scaffold under ``output_dir/lean_output``.

    Returns the project_dir path.
    """
    from vero.curation.lean_project import to_project_name

    project_name = to_project_name(benchmark_id)
    lean_output = output_dir / "lean_output"
    project_dir = lean_output / project_name
    impl_dir = project_dir / project_name / "Impl"
    impl_dir.mkdir(parents=True, exist_ok=True)
    (project_dir / project_name / "Spec").mkdir(parents=True, exist_ok=True)

    # Synthesize one Impl file with the requested code-block bodies.
    lines = [
        "-- !benchmark @start imports",
        "-- !benchmark @end imports",
        "",
        "namespace Demo",
        "",
    ]
    for api_name, body in impl_bodies.items():
        lines.extend(
            [
                f"abbrev {api_name.title()}Sig := Int → Int",
                f"def Demo.{api_name} : Demo.{api_name.title()}Sig :=",
                f"-- !benchmark @start code def={api_name}",
                f"  {body}",
                f"-- !benchmark @end code def={api_name}",
                "",
            ]
        )
    lines.append("end Demo")
    (impl_dir / "Demo.lean").write_text("\n".join(lines), encoding="utf-8")

    # Manifest stub (only structure the stage cares about is project_dir).
    (project_dir / "manifest.json").write_text(
        json.dumps(
            {
                "benchmark_id": benchmark_id,
                "root_package": project_name,
                "packages": [
                    {
                        "name": project_name,
                        "modules": [
                            {
                                "name": "Demo",
                                "impl": f"{project_name}/Impl/Demo.lean",
                                "spec": f"{project_name}/Spec/Demo.lean",
                                "apis": [
                                    {
                                        "name": k,
                                        "sig": f"{k.title()}Sig",
                                        "type": "Int → Int",
                                        "kind": "api",
                                    }
                                    for k in impl_bodies
                                ],
                                "specs": [],
                            }
                        ],
                    }
                ],
            }
        ),
        encoding="utf-8",
    )
    return project_dir


def _make_python_source(source_dir: Path, *, context: str = "original_python") -> Path:
    """Create a fake Python source tree under ``source_dir/<context>/``.

    Also writes a minimal ``benchmark.json`` so the stage can resolve the
    context path. Returns the python source dir.
    """
    src = source_dir / context
    src.mkdir(parents=True, exist_ok=True)
    (src / "demo.py").write_text("def double(x: int) -> int:\n    return x * 2\n")
    (source_dir / "benchmark.json").write_text(
        json.dumps(
            {
                "benchmark_id": "demo",
                "metadata": {"python_context_path": context},
            }
        ),
        encoding="utf-8",
    )
    return src


def _make_config(tmp_path: Path, *, benchmark_id: str = "demo") -> CurationConfig:
    src_dir = tmp_path / "src"
    src_dir.mkdir(parents=True, exist_ok=True)
    out_dir = tmp_path / "out"
    out_dir.mkdir(parents=True, exist_ok=True)
    return CurationConfig(
        benchmark_id=benchmark_id,
        source_language=SourceLanguage.PYTHON,
        source_dir=str(src_dir),
        output_dir=str(out_dir),
    )


# ─── _resolve_python_source_dir ─────────────────────────────────────


def test_resolve_python_source_dir_default(tmp_path: Path) -> None:
    cfg = _make_config(tmp_path)
    ctx = StageContext.from_config(cfg)
    # No benchmark.json: falls back to "original_python"
    resolved = _resolve_python_source_dir(ctx)
    assert resolved == ctx.source_dir / "original_python"


def test_resolve_python_source_dir_from_metadata(tmp_path: Path) -> None:
    cfg = _make_config(tmp_path)
    src = Path(cfg.source_dir)
    (src / "benchmark.json").write_text(
        json.dumps({"metadata": {"python_context_path": "py_src"}}),
        encoding="utf-8",
    )
    ctx = StageContext.from_config(cfg)
    resolved = _resolve_python_source_dir(ctx)
    assert resolved.name == "py_src"


def test_resolve_python_source_dir_null_metadata(tmp_path: Path) -> None:
    """When metadata.python_context_path is null, fall back to default."""
    cfg = _make_config(tmp_path)
    src = Path(cfg.source_dir)
    (src / "benchmark.json").write_text(
        json.dumps({"metadata": {"python_context_path": None}}),
        encoding="utf-8",
    )
    ctx = StageContext.from_config(cfg)
    resolved = _resolve_python_source_dir(ctx)
    assert resolved.name == "original_python"


# ─── count_unfilled_code_bodies ─────────────────────────────────────


def test_count_unfilled_code_bodies_all_sorry(tmp_path: Path) -> None:
    cfg = _make_config(tmp_path)
    project_dir = _make_scaffold(
        Path(cfg.output_dir),
        benchmark_id="demo",
        impl_bodies={"foo": "sorry", "bar": "sorry"},
    )
    assert count_unfilled_code_bodies(project_dir) == 2


def test_count_unfilled_code_bodies_all_filled(tmp_path: Path) -> None:
    cfg = _make_config(tmp_path)
    project_dir = _make_scaffold(
        Path(cfg.output_dir),
        benchmark_id="demo",
        impl_bodies={"foo": "fun x => x + 1", "bar": "fun x => x * 2"},
    )
    assert count_unfilled_code_bodies(project_dir) == 0


def test_count_unfilled_code_bodies_mixed(tmp_path: Path) -> None:
    cfg = _make_config(tmp_path)
    project_dir = _make_scaffold(
        Path(cfg.output_dir),
        benchmark_id="demo",
        impl_bodies={"foo": "sorry", "bar": "fun x => x + 1"},
    )
    assert count_unfilled_code_bodies(project_dir) == 1


def test_count_unfilled_code_bodies_no_manifest(tmp_path: Path) -> None:
    """No manifest → 0 (and not a crash)."""
    (tmp_path / "lean_output").mkdir()
    assert count_unfilled_code_bodies(tmp_path / "lean_output") == 0


def test_count_unfilled_code_bodies_uses_manifest_root_package(tmp_path: Path) -> None:
    """The package source dir is named by `manifest.json::root_package`, not by
    the lake-root directory's own name. ``_make_scaffold`` already uses the
    canonical ``<lake_root>/<Package>/Impl`` layout — this test pins that
    contract explicitly."""
    cfg = _make_config(tmp_path, benchmark_id="demo")
    project_dir = _make_scaffold(
        Path(cfg.output_dir),
        benchmark_id="demo",
        impl_bodies={"foo": "sorry", "bar": "fun x => x"},
    )
    # project_dir is `<output_dir>/lean_output/Demo`. manifest.root_package is
    # "Demo". Impl tree is `<project_dir>/Demo/Impl`.
    assert (project_dir / "Demo" / "Impl").exists()
    assert count_unfilled_code_bodies(project_dir) == 1


# ─── Stage dispatch ─────────────────────────────────────────────────


def test_stage_fails_when_project_dir_missing(tmp_path: Path) -> None:
    cfg = _make_config(tmp_path)
    ctx = StageContext.from_config(cfg)
    result = asyncio.run(PythonAdjustBodiesStage().run(ctx))
    assert result.success is False
    assert "Lean project not found" in result.error


def test_stage_fails_when_python_source_missing(tmp_path: Path) -> None:
    cfg = _make_config(tmp_path)
    _make_scaffold(
        Path(cfg.output_dir),
        benchmark_id="demo",
        impl_bodies={"foo": "sorry"},
    )
    ctx = StageContext.from_config(cfg)
    result = asyncio.run(PythonAdjustBodiesStage().run(ctx))
    assert result.success is False
    assert "Python source dir not found" in result.error


def test_stage_idempotent_on_filled_project(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """When all code-blocks have non-sorry bodies, skip the agent call."""
    cfg = _make_config(tmp_path)
    _make_scaffold(
        Path(cfg.output_dir),
        benchmark_id="demo",
        impl_bodies={"foo": "fun x => x + 1"},
    )
    _make_python_source(Path(cfg.source_dir))
    ctx = StageContext.from_config(cfg)

    called = {"agent": False}

    async def fake_agent(*args, **kwargs):  # noqa: ARG001
        called["agent"] = True
        return ([], "session-x")

    monkeypatch.setattr("vero.curation.agent.call_agent", fake_agent, raising=False)
    result = asyncio.run(PythonAdjustBodiesStage().run(ctx))
    assert result.success is True
    assert called["agent"] is False, "agent must not be called when nothing is unfilled"


def test_stage_calls_agent_when_sorry_remains(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """When code-blocks still hold `sorry`, the stage must invoke the agent and run lake build."""
    cfg = _make_config(tmp_path)
    _make_scaffold(
        Path(cfg.output_dir),
        benchmark_id="demo",
        impl_bodies={"foo": "sorry"},
    )
    _make_python_source(Path(cfg.source_dir))
    ctx = StageContext.from_config(cfg)

    captured = {}

    async def fake_agent(**kwargs):
        captured.update(kwargs)
        return ([], "session-y")

    async def fake_build(project_dir):  # noqa: ARG001
        return True, "ok"

    # Monkey-patch the stage module's bindings (the stage imports call_agent
    # locally inside run(), so we patch the symbol where it'll be looked up).
    import vero.curation.agent as agent_mod
    import vero.curation.stages.python_adjust_bodies as stage_mod

    monkeypatch.setattr(agent_mod, "call_agent", fake_agent)
    monkeypatch.setattr(stage_mod, "_run_lake_build", fake_build)

    # Pretend the agent filled the body — replace sorry post-hoc.
    project_dir = ctx.lean_output_dir / "Demo"
    impl_file = project_dir / "Demo" / "Impl" / "Demo.lean"

    async def fake_agent_with_fill(**kwargs):
        captured.update(kwargs)
        text = impl_file.read_text(encoding="utf-8")
        text = text.replace("  sorry", "  fun x => x + 1")
        impl_file.write_text(text, encoding="utf-8")
        return ([], "session-y")

    monkeypatch.setattr(agent_mod, "call_agent", fake_agent_with_fill)

    result = asyncio.run(PythonAdjustBodiesStage().run(ctx))
    assert result.success is True
    # Agent must have been called.
    assert "prompt" in captured
    # Prompt must reference the python source dir + project dir.
    prompt = captured["prompt"]
    assert "original_python" in prompt
    assert str(project_dir) in prompt


def test_stage_build_failure_returns_error(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    cfg = _make_config(tmp_path)
    _make_scaffold(
        Path(cfg.output_dir),
        benchmark_id="demo",
        impl_bodies={"foo": "sorry"},
    )
    _make_python_source(Path(cfg.source_dir))
    ctx = StageContext.from_config(cfg)

    async def fake_agent(**kwargs):  # noqa: ARG001
        return ([], "session-z")

    async def fake_build_fail(project_dir):  # noqa: ARG001
        return False, "type mismatch at Demo.lean:5"

    import vero.curation.agent as agent_mod
    import vero.curation.stages.python_adjust_bodies as stage_mod

    monkeypatch.setattr(agent_mod, "call_agent", fake_agent)
    monkeypatch.setattr(stage_mod, "_run_lake_build", fake_build_fail)

    result = asyncio.run(PythonAdjustBodiesStage().run(ctx))
    assert result.success is False
    assert "type mismatch" in result.error


def test_stage_detects_remaining_sorrys_after_build(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """If lake build passes but code-blocks still contain sorry, mark failure.

    This is the case where the agent committed to compiling sorry stubs
    instead of actual translations (`Build completed with sorry warnings`).
    """
    cfg = _make_config(tmp_path)
    _make_scaffold(
        Path(cfg.output_dir),
        benchmark_id="demo",
        impl_bodies={"foo": "sorry", "bar": "sorry"},
    )
    _make_python_source(Path(cfg.source_dir))
    ctx = StageContext.from_config(cfg)

    async def fake_agent(**kwargs):  # noqa: ARG001
        return ([], "session-q")

    async def fake_build_ok(project_dir):  # noqa: ARG001
        return True, "warning: declaration uses sorry"

    import vero.curation.agent as agent_mod
    import vero.curation.stages.python_adjust_bodies as stage_mod

    monkeypatch.setattr(agent_mod, "call_agent", fake_agent)
    monkeypatch.setattr(stage_mod, "_run_lake_build", fake_build_ok)

    result = asyncio.run(PythonAdjustBodiesStage().run(ctx))
    assert result.success is False
    assert "still contain `sorry`" in result.error


# ─── Pipeline wiring ─────────────────────────────────────────────────


def test_pipeline_includes_adjust_bodies_in_legacy_scaffold_pipeline() -> None:
    """The deterministic two-phase pipeline (scaffold → adjust-bodies →
    spec_write → validate) is preserved as ``PythonFromBenchmarkJsonScaffoldPipeline``
    for callers that explicitly want the mechanical-scaffold route.
    The default ``PythonFromBenchmarkJsonPipeline`` is now agent-driven;
    see ``test_python_curate.py`` for that pipeline's shape."""
    from vero.curation.pipeline import (
        PythonAdjustBodiesStage as _PASInPipelineModule,  # re-import via pipeline.py
    )
    from vero.curation.pipeline import PythonFromBenchmarkJsonScaffoldPipeline
    from vero.curation.stages.python_from_json import PythonFromJsonStage
    from vero.curation.stages.spec_write import SpecWriteStage
    from vero.curation.stages.validate import ValidateStage

    stages = PythonFromBenchmarkJsonScaffoldPipeline.stages
    names = [s.name for s in stages]
    assert names == [
        PythonFromJsonStage.name,
        PythonAdjustBodiesStage.name,
        SpecWriteStage.name,
        ValidateStage.name,
    ]
    # PythonAdjustBodiesStage must be the same class regardless of import path.
    assert stages[1] is _PASInPipelineModule
    assert stages[1] is PythonAdjustBodiesStage


def test_max_turns_python_adjust_default() -> None:
    cfg = CurationConfig(source_dir="/tmp/x", output_dir="/tmp/y")
    assert cfg.max_turns_python_adjust == 100
