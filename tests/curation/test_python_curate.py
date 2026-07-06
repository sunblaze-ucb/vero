"""Tests for ``PythonCurateStage`` (agent-driven mode-A curation)."""

from __future__ import annotations

import asyncio
import json
from pathlib import Path

import pytest

from vero.curation.config import CurationConfig
from vero.curation.models import SourceLanguage
from vero.curation.stages.base import StageContext
from vero.curation.stages.python_curate import PythonCurateStage

# ─── Fixtures (mirror tests/curation/test_python_adjust_bodies.py) ──


def _make_scaffold(
    output_dir: Path,
    *,
    benchmark_id: str,
    impl_bodies: dict[str, str],
) -> Path:
    from vero.curation.lean_project import to_project_name

    project_name = to_project_name(benchmark_id)
    lean_output = output_dir / "lean_output"
    project_dir = lean_output / project_name
    impl_dir = project_dir / project_name / "Impl"
    impl_dir.mkdir(parents=True, exist_ok=True)
    (project_dir / project_name / "Spec").mkdir(parents=True, exist_ok=True)
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
    # Spec/Demo.lean stub so the manifest round-trip check (which requires
    # the declared spec file to exist on disk) passes by default. Tests
    # that want to exercise the missing-spec path overwrite manifest.json
    # to point at a non-existent path.
    (project_dir / project_name / "Spec" / "Demo.lean").write_text(
        f"namespace {project_name}\n-- specs filled by spec_write stage\nend {project_name}\n",
        encoding="utf-8",
    )
    (project_dir / "manifest.json").write_text(
        json.dumps(
            {
                "benchmark_id": benchmark_id,
                "lean_version": "4.29.1",
                "modes_supported": ["proof", "codeproof"],
                "source": {"language": "python"},
                "curation": {},
                "files": {
                    "root_hub": f"{project_name}.lean",
                    "harness": f"{project_name}/Harness.lean",
                    "test": f"{project_name}/Test.lean",
                    "lakefile": "lakefile.toml",
                },
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


# ─── Stage dispatch ──────────────────────────────────────────────────


def test_stage_fails_when_benchmark_json_missing(tmp_path: Path) -> None:
    """Without ``benchmark.json`` the stage cannot even brief the agent."""
    cfg = _make_config(tmp_path)
    # Source dir intentionally empty — no benchmark.json.
    ctx = StageContext.from_config(cfg)
    result = asyncio.run(PythonCurateStage().run(ctx))
    assert result.success is False
    assert "benchmark.json not found" in result.error


def test_stage_fails_when_python_source_missing(tmp_path: Path) -> None:
    cfg = _make_config(tmp_path)
    src = Path(cfg.source_dir)
    (src / "benchmark.json").write_text(
        json.dumps({"benchmark_id": "demo", "metadata": {}}),
        encoding="utf-8",
    )
    ctx = StageContext.from_config(cfg)
    result = asyncio.run(PythonCurateStage().run(ctx))
    assert result.success is False
    assert "Python source dir not found" in result.error


def test_stage_idempotent_on_clean_filled_project(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """When the project already exists, builds clean, and has no sorry in
    code blocks, the stage skips the agent call entirely."""
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

    async def fake_build_ok(project_dir):  # noqa: ARG001
        return True, "ok"

    import vero.curation.agent as agent_mod
    import vero.curation.stages.python_curate as stage_mod

    monkeypatch.setattr(agent_mod, "call_agent", fake_agent)
    monkeypatch.setattr(stage_mod, "_run_lake_build", fake_build_ok)

    result = asyncio.run(PythonCurateStage().run(ctx))
    assert result.success is True
    assert called["agent"] is False, (
        "agent must not be called when project already curated"
    )


def test_stage_calls_agent_when_project_is_missing(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """When no project exists yet, the agent is invoked and the prompt
    references both benchmark.json (reference) and original_python (truth)."""
    cfg = _make_config(tmp_path)
    _make_python_source(Path(cfg.source_dir))
    ctx = StageContext.from_config(cfg)

    captured: dict[str, object] = {}

    async def fake_agent(**kwargs):
        captured.update(kwargs)
        # Pretend the agent created the project and filled all bodies.
        _make_scaffold(
            Path(cfg.output_dir),
            benchmark_id="demo",
            impl_bodies={"foo": "fun x => x + 1"},
        )
        return ([], "session-y")

    async def fake_build_ok(project_dir):  # noqa: ARG001
        return True, "ok"

    import vero.curation.agent as agent_mod
    import vero.curation.stages.python_curate as stage_mod

    monkeypatch.setattr(agent_mod, "call_agent", fake_agent)
    monkeypatch.setattr(stage_mod, "_run_lake_build", fake_build_ok)

    result = asyncio.run(PythonCurateStage().run(ctx))
    assert result.success is True
    prompt = captured.get("prompt", "")
    assert isinstance(prompt, str)
    assert "benchmark.json" in prompt
    assert "original_python" in prompt
    assert "reference/BankLedger" in prompt
    # The prompt must explicitly tell the agent to use Lean's `variable`
    # for generic handling — this is the load-bearing rule that distinguishes
    # the new stage from the deterministic scaffolder.
    assert "variable" in prompt
    # Spec files must be stubs at this stage.
    assert "spec_write" in prompt.lower() or "spec stage" in prompt.lower()


def test_stage_build_failure_returns_error(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    cfg = _make_config(tmp_path)
    _make_python_source(Path(cfg.source_dir))
    ctx = StageContext.from_config(cfg)

    async def fake_agent(**kwargs):  # noqa: ARG001
        _make_scaffold(
            Path(cfg.output_dir),
            benchmark_id="demo",
            impl_bodies={"foo": "fun x => x + bogus_identifier"},
        )
        return ([], "session-z")

    async def fake_build_fail(project_dir):  # noqa: ARG001
        return False, "unknown identifier 'bogus_identifier'"

    import vero.curation.agent as agent_mod
    import vero.curation.stages.python_curate as stage_mod

    monkeypatch.setattr(agent_mod, "call_agent", fake_agent)
    monkeypatch.setattr(stage_mod, "_run_lake_build", fake_build_fail)

    result = asyncio.run(PythonCurateStage().run(ctx))
    assert result.success is False
    assert "unknown identifier" in result.error


def test_stage_detects_remaining_sorrys_after_build(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """Build passes but at least one code-block still says ``sorry``: failure."""
    cfg = _make_config(tmp_path)
    _make_python_source(Path(cfg.source_dir))
    ctx = StageContext.from_config(cfg)

    async def fake_agent(**kwargs):  # noqa: ARG001
        _make_scaffold(
            Path(cfg.output_dir),
            benchmark_id="demo",
            impl_bodies={"foo": "sorry"},
        )
        return ([], "session-q")

    async def fake_build_ok(project_dir):  # noqa: ARG001
        return True, "warning: declaration uses sorry"

    import vero.curation.agent as agent_mod
    import vero.curation.stages.python_curate as stage_mod

    monkeypatch.setattr(agent_mod, "call_agent", fake_agent)
    monkeypatch.setattr(stage_mod, "_run_lake_build", fake_build_ok)

    result = asyncio.run(PythonCurateStage().run(ctx))
    assert result.success is False
    assert "still contain `sorry`" in result.error


def test_stage_rejects_empty_manifest(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """Build OK + bodies filled is not enough — manifest.json must round-trip
    too. The agent has been observed to leave `manifest.json = {}` when it
    runs out of turn budget; this test pins the check that catches it."""
    cfg = _make_config(tmp_path)
    _make_python_source(Path(cfg.source_dir))
    ctx = StageContext.from_config(cfg)

    async def fake_agent(**kwargs):  # noqa: ARG001
        # Scaffold + fill bodies, but leave manifest.json as `{}`.
        proj = _make_scaffold(
            Path(cfg.output_dir),
            benchmark_id="demo",
            impl_bodies={"foo": "fun x => x + 1"},
        )
        # Override the manifest with an empty object.
        (proj / "manifest.json").write_text("{}", encoding="utf-8")
        return ([], "session-em")

    async def fake_build_ok(project_dir):  # noqa: ARG001
        return True, "ok"

    import vero.curation.agent as agent_mod
    import vero.curation.stages.python_curate as stage_mod

    monkeypatch.setattr(agent_mod, "call_agent", fake_agent)
    monkeypatch.setattr(stage_mod, "_run_lake_build", fake_build_ok)

    result = asyncio.run(PythonCurateStage().run(ctx))
    assert result.success is False
    assert "manifest.json missing required" in result.error


def test_stage_rejects_missing_spec_file(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """If manifest.json declares a Spec/<Module>.lean that doesn't exist on
    disk, the curate stage must fail. (Build can be clean because the
    Bundle/Harness/Impl files alone compile.)"""
    cfg = _make_config(tmp_path)
    _make_python_source(Path(cfg.source_dir))
    ctx = StageContext.from_config(cfg)

    async def fake_agent(**kwargs):  # noqa: ARG001
        proj = _make_scaffold(
            Path(cfg.output_dir),
            benchmark_id="demo",
            impl_bodies={"foo": "fun x => x + 1"},
        )
        # _make_scaffold creates Demo/Spec/Demo.lean by default; delete it
        # to exercise the missing-spec-file failure path.
        (proj / "Demo" / "Spec" / "Demo.lean").unlink(missing_ok=True)
        (proj / "manifest.json").write_text(
            json.dumps(
                {
                    "benchmark_id": "demo",
                    "lean_version": "4.29.1",
                    "modes_supported": ["proof"],
                    "source": {},
                    "curation": {},
                    "files": {
                        "root_hub": "Demo.lean",
                        "harness": "Demo/Harness.lean",
                        "test": "Demo/Test.lean",
                        "lakefile": "lakefile.toml",
                    },
                    "root_package": "Demo",
                    "packages": [
                        {
                            "name": "Demo",
                            "modules": [
                                {
                                    "name": "Demo",
                                    "impl": "Demo/Impl/Demo.lean",
                                    "spec": "Demo/Spec/Demo.lean",
                                    "apis": [],
                                    "specs": [],
                                }
                            ],
                        }
                    ],
                }
            ),
            encoding="utf-8",
        )
        return ([], "session-spec")

    async def fake_build_ok(project_dir):  # noqa: ARG001
        return True, "ok"

    import vero.curation.agent as agent_mod
    import vero.curation.stages.python_curate as stage_mod

    monkeypatch.setattr(agent_mod, "call_agent", fake_agent)
    monkeypatch.setattr(stage_mod, "_run_lake_build", fake_build_ok)

    result = asyncio.run(PythonCurateStage().run(ctx))
    assert result.success is False
    assert "declared spec file does not exist" in result.error


def test_stage_writes_benchmark_id_back_when_missing(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """If the curation config has no ``benchmark_id``, the stage reads it
    from ``benchmark.json`` and persists it via ``config.save()`` so
    downstream stages can resolve ``lean_output_dir / <Project>``."""
    src_dir = tmp_path / "src"
    out_dir = tmp_path / "out"
    src_dir.mkdir()
    out_dir.mkdir()
    cfg = CurationConfig(
        benchmark_id="",  # <-- empty
        source_language=SourceLanguage.PYTHON,
        source_dir=str(src_dir),
        output_dir=str(out_dir),
    )

    # Write benchmark.json with a real benchmark_id.
    (src_dir / "benchmark.json").write_text(
        json.dumps(
            {"benchmark_id": "bidict", "metadata": {"python_context_path": "py"}}
        ),
        encoding="utf-8",
    )
    (src_dir / "py").mkdir()
    (src_dir / "py" / "demo.py").write_text("def f(): pass\n")

    ctx = StageContext.from_config(cfg)

    async def fake_agent(**kwargs):  # noqa: ARG001
        # Agent creates a minimal project at the *post-update* path.
        _make_scaffold(
            Path(cfg.output_dir),
            benchmark_id="bidict",
            impl_bodies={"foo": "fun x => x"},
        )
        return ([], "session-bid")

    async def fake_build_ok(project_dir):  # noqa: ARG001
        return True, "ok"

    import vero.curation.agent as agent_mod
    import vero.curation.stages.python_curate as stage_mod

    monkeypatch.setattr(agent_mod, "call_agent", fake_agent)
    monkeypatch.setattr(stage_mod, "_run_lake_build", fake_build_ok)

    result = asyncio.run(PythonCurateStage().run(ctx))
    assert result.success is True
    assert cfg.benchmark_id == "bidict"


# ─── Pipeline wiring ─────────────────────────────────────────────────


def test_pipeline_default_is_agent_driven() -> None:
    """``PythonFromBenchmarkJsonPipeline`` (the default workflow) now uses
    only the agent-driven curate stage. ``spec_write`` and ``validate``
    are intentionally absent at this point per user direction 2026-04-26;
    both run separately as ad-hoc sweeps once curate has stabilised."""
    from vero.curation.pipeline import (
        PythonCurateStage as _PCSPipeline,  # re-import via pipeline.py
    )
    from vero.curation.pipeline import PythonFromBenchmarkJsonPipeline

    stages = PythonFromBenchmarkJsonPipeline.stages
    names = [s.name for s in stages]
    assert names == [PythonCurateStage.name]
    # Same class regardless of import path.
    assert stages[0] is _PCSPipeline
    assert stages[0] is PythonCurateStage


def test_pipeline_legacy_scaffold_workflow_registered() -> None:
    """The legacy two-phase workflow is registered under
    ``python_from_benchmark_json_scaffold`` so callers can still opt in."""
    from vero.curation.pipeline import (
        WORKFLOWS,
        PythonFromBenchmarkJsonScaffoldPipeline,
    )

    assert "python_from_benchmark_json_scaffold" in WORKFLOWS
    assert WORKFLOWS["python_from_benchmark_json_scaffold"] is (
        PythonFromBenchmarkJsonScaffoldPipeline
    )


def test_max_turns_python_curate_default() -> None:
    cfg = CurationConfig(source_dir="/tmp/x", output_dir="/tmp/y")
    assert cfg.max_turns_python_curate == 200
