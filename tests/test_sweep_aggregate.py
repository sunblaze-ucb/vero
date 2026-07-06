"""Tests for `vero.sweep_aggregate`."""

from __future__ import annotations

import json
from pathlib import Path

from vero.sweep_aggregate import collect, write_csv, write_json, write_md


def _make_run(
    root: Path,
    name: str,
    benchmark_id: str,
    agent_kind: str,
    agent_model: str,
    mode: str,
    eval_name: str,
    *,
    build_ok: bool = True,
    impl_broken: bool = False,
    total: int = 11,
    passed: int = 7,
    unfilled: int = 2,
    failed: int = 2,
    joint: bool | None = None,
) -> None:
    run_dir = root / name
    run_dir.mkdir(parents=True)
    (run_dir / "manifest.json").write_text(
        json.dumps(
            {
                "name": name,
                "benchmark_id": benchmark_id,
                "benchmark_path": f"/tmp/{benchmark_id}",
                "mode": mode,
                "agent": {"kind": agent_kind, "model": agent_model},
                "created_at": "2026-04-22T18:00:00",
                "git_sha": "deadbeef",
            }
        )
    )
    eval_dir = run_dir / "eval" / eval_name
    eval_dir.mkdir(parents=True)
    summary = {
        "total_specs": total,
        "passed_specs": passed,
        "unfilled_specs": unfilled,
        "overfilled_specs": 0,
        "failed_specs": failed,
        "unpaired_sat_specs": 0,
        "joint_passed": joint if joint is not None else False,
    }
    joint_obj = (
        {
            "status": ("ok" if joint else "fail"),
            "specs": [],
            "theorem_name": None,
            "notes": "",
        }
        if joint is not None
        else None
    )
    (eval_dir / "report.json").write_text(
        json.dumps(
            {
                "benchmark_id": benchmark_id,
                "mode": mode,
                "sandbox_dir": "/tmp/sandbox",
                "build": {
                    "ok": build_ok,
                    "tail": "",
                    "impl_broken": impl_broken,
                    "impl_broken_reason": "",
                },
                "summary": summary,
                "specs": [],
                "joint": joint_obj,
                "axiom_checks": [],
            }
        )
    )


def test_collect_single_run(tmp_path: Path) -> None:
    _make_run(tmp_path, "r1", "bankledger", "claude", "sonnet", "proof", "default")
    cells = collect(tmp_path)
    assert len(cells) == 1
    c = cells[0]
    assert c.benchmark_id == "bankledger"
    assert c.agent_kind == "claude"
    assert c.agent_model == "sonnet"
    assert c.mode == "proof"
    assert c.eval_name == "default"
    assert c.total_specs == 11
    assert c.passed_specs == 7
    assert abs(c.pass_rate - 7 / 11) < 1e-9


def test_collect_multi_runs_sorted(tmp_path: Path) -> None:
    _make_run(tmp_path, "r1", "bankledger", "claude", "sonnet-4-6", "proof", "default")
    _make_run(
        tmp_path,
        "r2",
        "deposit_sc",
        "codex",
        "gpt5.4",
        "codeproof",
        "default",
        joint=True,
    )
    cells = collect(tmp_path)
    assert len(cells) == 2
    kinds = sorted(c.agent_kind for c in cells)
    assert kinds == ["claude", "codex"]
    # The codex/codeproof cell should have joint_passed=True (serializable via dict).
    codex_cell = next(c for c in cells if c.agent_kind == "codex")
    assert codex_cell.joint_passed is True


def test_collect_multi_evals_per_run(tmp_path: Path) -> None:
    """One run with two separate eval subdirs (e.g., default + strict) → two cells."""
    _make_run(tmp_path, "r1", "bankledger", "claude", "sonnet", "proof", "default")
    # Second eval under the same run
    eval_dir = tmp_path / "r1" / "eval" / "strict"
    eval_dir.mkdir(parents=True)
    (eval_dir / "report.json").write_text(
        json.dumps(
            {
                "benchmark_id": "bankledger",
                "mode": "proof",
                "sandbox_dir": "/tmp",
                "build": {
                    "ok": True,
                    "tail": "",
                    "impl_broken": False,
                    "impl_broken_reason": "",
                },
                "summary": {
                    "total_specs": 11,
                    "passed_specs": 9,
                    "unfilled_specs": 0,
                    "overfilled_specs": 0,
                    "failed_specs": 2,
                    "unpaired_sat_specs": 0,
                    "joint_passed": False,
                },
                "specs": [],
                "joint": None,
                "axiom_checks": [],
            }
        )
    )
    cells = collect(tmp_path)
    assert len(cells) == 2
    names = sorted(c.eval_name for c in cells)
    assert names == ["default", "strict"]


def test_collect_skips_incomplete_runs(tmp_path: Path) -> None:
    """A dir without manifest.json is silently ignored."""
    (tmp_path / "garbage").mkdir()
    _make_run(tmp_path, "r1", "bankledger", "claude", "sonnet", "proof", "default")
    cells = collect(tmp_path)
    assert len(cells) == 1


def test_collect_handles_impl_broken(tmp_path: Path) -> None:
    _make_run(
        tmp_path,
        "broken",
        "verdict",
        "codex",
        "gpt5.4",
        "codeproof",
        "default",
        build_ok=False,
        impl_broken=True,
        passed=0,
        unfilled=120,
        failed=0,
    )
    cells = collect(tmp_path)
    assert cells[0].impl_broken is True
    assert cells[0].pass_rate == 0.0


def test_write_csv_header_and_rows(tmp_path: Path) -> None:
    _make_run(tmp_path, "r1", "bankledger", "claude", "sonnet", "proof", "default")
    _make_run(tmp_path, "r2", "deposit_sc", "codex", "gpt5.4", "codeproof", "default")
    cells = collect(tmp_path)
    out = tmp_path / "results.csv"
    write_csv(cells, out)
    text = out.read_text()
    assert "benchmark_id" in text.splitlines()[0]
    assert "bankledger" in text
    assert "deposit_sc" in text


def test_write_json_and_md_roundtrip(tmp_path: Path) -> None:
    _make_run(tmp_path, "r1", "bankledger", "claude", "sonnet", "proof", "default")
    cells = collect(tmp_path)
    json_out = tmp_path / "results.json"
    write_json(cells, json_out)
    data = json.loads(json_out.read_text())
    assert len(data["cells"]) == 1
    md_out = tmp_path / "results.md"
    write_md(cells, md_out)
    md = md_out.read_text()
    assert "bankledger" in md
    assert "Sweep results" in md


def test_write_md_empty_sweep(tmp_path: Path) -> None:
    out = tmp_path / "results.md"
    write_md([], out)
    assert "Total cells: **0**" in out.read_text()
