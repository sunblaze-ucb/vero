"""``vero-extract`` — build an ``artifact.json`` from an (edited) sandbox.

For the "bring your own agent" decoupled flow: after your agent edits the
``!benchmark`` marker slots in a rendered sandbox, run this to parse those
edits into ``artifact.json``, then grade with ``vero run run=<name>``.

Usage:

    # From a run rendered with `vero run ... skip_agent=true skip_eval=true name=<run>`
    # (reads the run's frozen run.yaml for the benchmark + mode):
    vero-extract --run <run>

    # Or point at a sandbox explicitly:
    vero-extract --sandbox <dir> --benchmark benchmarks/bankledger --mode codeproof
"""

from __future__ import annotations

import argparse
from pathlib import Path

from vero.cli import REPO_ROOT, _resolve_under_repo
from vero.generation.benchmark import Benchmark
from vero.generation.extractor import extract, write_artifact


def _resolve_run_dir(name: str) -> Path:
    for root in (REPO_ROOT / "agent_runs", REPO_ROOT / "saved_agent_runs"):
        cand = root / name
        if (cand / "run.yaml").is_file():
            return cand
    raise SystemExit(
        f"no run.yaml for run {name!r} under agent_runs/ or saved_agent_runs/"
    )


def main() -> int:
    ap = argparse.ArgumentParser(
        prog="vero-extract",
        description="Extract artifact.json from an (edited) benchmark sandbox.",
    )
    ap.add_argument(
        "--run",
        help="run name under agent_runs/ (reads its run.yaml for benchmark + mode; "
        "extracts from <run>/source/ into <run>/source/artifact.json)",
    )
    ap.add_argument(
        "--sandbox",
        type=Path,
        help="path to the sandbox the agent edited (the 'source/' tree)",
    )
    ap.add_argument(
        "--benchmark",
        type=Path,
        help="path to the source benchmark dir (e.g. benchmarks/bankledger)",
    )
    ap.add_argument("--mode", choices=["proof", "codeproof"], help="evaluation mode")
    ap.add_argument(
        "--out",
        type=Path,
        help="output artifact path (default: <sandbox>/artifact.json)",
    )
    args = ap.parse_args()

    if args.run:
        from omegaconf import OmegaConf

        run_dir = _resolve_run_dir(args.run)
        cfg = OmegaConf.load(run_dir / "run.yaml")
        sandbox = run_dir / "source"
        benchmark_dir = _resolve_under_repo(str(cfg.benchmark.path))
        mode = args.mode or str(cfg.mode)
    else:
        if not (args.sandbox and args.benchmark and args.mode):
            ap.error("provide --run, or all of --sandbox / --benchmark / --mode")
        sandbox = args.sandbox
        benchmark_dir = args.benchmark
        mode = args.mode

    if not (sandbox / "INSTRUCTION.md").is_file():
        raise SystemExit(
            f"{sandbox} does not look like a rendered sandbox (no INSTRUCTION.md)"
        )

    out = args.out or (sandbox / "artifact.json")
    artifact = extract(sandbox, Benchmark(benchmark_dir), mode=mode)
    write_artifact(artifact, out)
    found = sum(1 for s in artifact.slots if getattr(s, "found", False))
    print(f"extracted {found}/{len(artifact.slots)} slots from {sandbox} → {out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
