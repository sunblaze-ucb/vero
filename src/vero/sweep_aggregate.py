"""Aggregate evaluation results from a multirun directory.

`vero run -m benchmark=a,b agent=x,y mode=proof,codeproof` writes each
variant under `agent_runs/<name>/`; a Hydra multirun landing dir groups
them under a timestamped parent. This module walks any directory of
runs and emits `results.json` + `results.csv` + `results.md` summarising
build ok / specs passed / unfilled / failed / joint-passed / cost per
(benchmark, agent, model, mode, eval-name) cell.

Used as a console script via `vero-sweep-aggregate`.
"""

from __future__ import annotations

import argparse
import csv
import json
import sys
from dataclasses import dataclass
from pathlib import Path


@dataclass
class RunCell:
    run_name: str
    benchmark_id: str
    mode: str
    agent_kind: str
    agent_model: str | None
    eval_name: str
    build_ok: bool
    impl_broken: bool
    total_specs: int
    passed_specs: int
    unfilled_specs: int
    overfilled_specs: int
    failed_specs: int
    joint_passed: bool | None
    report_path: str

    @property
    def pass_rate(self) -> float:
        return self.passed_specs / self.total_specs if self.total_specs else 0.0


def _load_manifest(run_dir: Path) -> dict | None:
    p = run_dir / "manifest.json"
    if not p.exists():
        return None
    try:
        return json.loads(p.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, OSError):
        return None


def _iter_eval_reports(run_dir: Path):
    """Yield (eval_name, report_dict) for every eval under this run."""
    eval_dir = run_dir / "eval"
    if not eval_dir.is_dir():
        return
    for sub in sorted(eval_dir.iterdir()):
        if not sub.is_dir():
            continue
        report_path = sub / "report.json"
        if not report_path.exists():
            continue
        try:
            yield (
                sub.name,
                json.loads(report_path.read_text(encoding="utf-8")),
                report_path,
            )
        except (json.JSONDecodeError, OSError):
            continue


def collect(sweep_root: Path) -> list[RunCell]:
    """Walk a sweep root and collect one RunCell per (run, eval-name)."""
    cells: list[RunCell] = []
    # Sweep root may be either a run dir (single run) or a parent of run dirs.
    # Runs are identified by the presence of `manifest.json`.
    candidates: list[Path] = []
    if (sweep_root / "manifest.json").exists():
        candidates.append(sweep_root)
    else:
        for sub in sorted(sweep_root.iterdir()):
            if sub.is_dir() and (sub / "manifest.json").exists():
                candidates.append(sub)

    for run_dir in candidates:
        manifest = _load_manifest(run_dir)
        if manifest is None:
            continue
        for eval_name, report, report_path in _iter_eval_reports(run_dir):
            build = report.get("build", {})
            summary = report.get("summary", {})
            joint = report.get("joint")
            cells.append(
                RunCell(
                    run_name=manifest.get("name", run_dir.name),
                    benchmark_id=manifest.get("benchmark_id")
                    or report.get("benchmark_id", ""),
                    mode=manifest.get("mode") or report.get("mode", ""),
                    agent_kind=manifest.get("agent", {}).get("kind", ""),
                    agent_model=manifest.get("agent", {}).get("model"),
                    eval_name=eval_name,
                    build_ok=bool(build.get("ok", False)),
                    impl_broken=bool(build.get("impl_broken", False)),
                    total_specs=int(summary.get("total_specs", 0)),
                    passed_specs=int(summary.get("passed_specs", 0)),
                    unfilled_specs=int(summary.get("unfilled_specs", 0)),
                    overfilled_specs=int(summary.get("overfilled_specs", 0)),
                    failed_specs=int(summary.get("failed_specs", 0)),
                    joint_passed=(
                        bool(summary.get("joint_passed")) if joint is not None else None
                    ),
                    report_path=str(report_path.relative_to(sweep_root)),
                )
            )
    return cells


_CSV_HEADER = [
    "benchmark_id",
    "agent_kind",
    "agent_model",
    "mode",
    "eval_name",
    "build_ok",
    "impl_broken",
    "total_specs",
    "passed_specs",
    "unfilled_specs",
    "overfilled_specs",
    "failed_specs",
    "pass_rate",
    "joint_passed",
    "run_name",
    "report_path",
]


def write_csv(cells: list[RunCell], path: Path) -> None:
    with path.open("w", encoding="utf-8", newline="") as fh:
        w = csv.writer(fh)
        w.writerow(_CSV_HEADER)
        for c in cells:
            w.writerow(
                [
                    c.benchmark_id,
                    c.agent_kind,
                    c.agent_model or "",
                    c.mode,
                    c.eval_name,
                    c.build_ok,
                    c.impl_broken,
                    c.total_specs,
                    c.passed_specs,
                    c.unfilled_specs,
                    c.overfilled_specs,
                    c.failed_specs,
                    f"{c.pass_rate:.4f}",
                    "" if c.joint_passed is None else c.joint_passed,
                    c.run_name,
                    c.report_path,
                ]
            )


def write_json(cells: list[RunCell], path: Path) -> None:
    path.write_text(
        json.dumps(
            {"cells": [c.__dict__ | {"pass_rate": c.pass_rate} for c in cells]},
            indent=2,
        ),
        encoding="utf-8",
    )


def write_md(cells: list[RunCell], path: Path) -> None:
    lines = ["# Sweep results", ""]
    lines.append(f"Total cells: **{len(cells)}**")
    lines.append("")
    if not cells:
        path.write_text("\n".join(lines) + "\n", encoding="utf-8")
        return
    # Simple flat matrix; users with more structure can pivot the CSV.
    lines.append(
        "| Benchmark | Agent | Model | Mode | Eval | Build | Specs (P/T) | Pass % | Unfilled | Failed | Joint |"
    )
    lines.append("|---|---|---|---|---|---|---|---|---|---|---|")
    for c in sorted(
        cells, key=lambda x: (x.benchmark_id, x.agent_kind, x.mode, x.eval_name)
    ):
        build = "impl_broken" if c.impl_broken else ("✅" if c.build_ok else "❌")
        joint = "—" if c.joint_passed is None else ("✅" if c.joint_passed else "❌")
        lines.append(
            "| `{bench}` | `{agent}` | `{model}` | `{mode}` | `{eval}` | {build} "
            "| {p}/{t} | {pct:.1f}% | {unf} | {fail} | {joint} |".format(
                bench=c.benchmark_id,
                agent=c.agent_kind,
                model=c.agent_model or "",
                mode=c.mode,
                eval=c.eval_name,
                build=build,
                p=c.passed_specs,
                t=c.total_specs,
                pct=100 * c.pass_rate,
                unf=c.unfilled_specs,
                fail=c.failed_specs,
                joint=joint,
            )
        )
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        prog="vero-sweep-aggregate",
        description=(
            "Aggregate evaluation reports from a sweep of `vero run` "
            "invocations into CSV / JSON / Markdown tables."
        ),
    )
    parser.add_argument(
        "sweep_root",
        type=Path,
        help="Directory containing run subdirs (each with manifest.json + eval/*).",
    )
    parser.add_argument(
        "--out-dir",
        type=Path,
        default=None,
        help="Where to write results.{csv,json,md} (default: sweep_root).",
    )
    args = parser.parse_args(argv)

    sweep_root = args.sweep_root.resolve()
    if not sweep_root.is_dir():
        print(f"error: {sweep_root} is not a directory", file=sys.stderr)
        return 2
    out_dir = (args.out_dir or sweep_root).resolve()
    out_dir.mkdir(parents=True, exist_ok=True)

    cells = collect(sweep_root)
    write_csv(cells, out_dir / "results.csv")
    write_json(cells, out_dir / "results.json")
    write_md(cells, out_dir / "results.md")
    print(
        f"aggregated {len(cells)} cell(s) from {sweep_root} → "
        f"{out_dir}/results.{{csv,json,md}}"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
