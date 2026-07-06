"""CLI entry point for the curation pipeline.

Usage:
    python -m vero.curation run /path/to/source output/project --lang dafny
    python -m vero.curation run output/project --stage select
    python -m vero.curation run output/project --stage translate --force
    python -m vero.curation run output/project --stage translate --continue
    python -m vero.curation status output/project
    python -m vero.curation extract output/project/lean_output/
"""

from __future__ import annotations

import argparse
import json
import sys

import anyio

from vero.curation.config import CurationConfig
from vero.curation.models import SourceLanguage
from vero.curation.pipeline import WORKFLOWS, get_pipeline
from vero.curation.validation.llm_review import (
    LLM_REVIEW_CHECKS,
    promote_memory_candidates,
)


def _load_env_creds() -> None:
    """Load `.env` from the upstream repo (worktree-aware) so the agent can
    read `LLM_API_KEY` / `LLM_API_BASE`. Mirrors `vero.cli._find_env_file`.
    """
    import os
    from pathlib import Path

    try:
        from dotenv import load_dotenv
    except ImportError:
        return
    explicit = os.environ.get("VERO_ENV_FILE")
    if explicit:
        p = Path(explicit).expanduser()
        if p.is_file():
            load_dotenv(p, override=False)
            return
    repo_root = Path(__file__).resolve().parents[3]
    primary = repo_root / ".env"
    if primary.is_file():
        load_dotenv(primary, override=False)
        return
    git_marker = repo_root / ".git"
    if git_marker.is_file():
        try:
            text = git_marker.read_text(encoding="utf-8").strip()
            if text.startswith("gitdir:"):
                gitdir = Path(text.split(":", 1)[1].strip())
                upstream = gitdir.parent.parent.parent
                candidate = upstream / ".env"
                if candidate.is_file():
                    load_dotenv(candidate, override=False)
                    return
        except OSError:
            pass


def _env_agent_creds() -> tuple[str | None, str | None]:
    """Return env-derived API key/base URL for curation agent calls."""
    import os

    llm_key = os.environ.get("LLM_API_KEY") or os.environ.get("ANTHROPIC_API_KEY")
    llm_base = os.environ.get("LLM_API_BASE") or os.environ.get("ANTHROPIC_BASE_URL")
    return llm_key, llm_base


def _redact_local_codex_credentials(config: CurationConfig) -> None:
    """Local Codex auth must not persist proxy/API credentials in config.yaml."""
    if config.agent_kind == "codex" and config.codex_auth_mode == "local":
        config.api_key = None
        config.api_base_url = None


def cmd_run(args: argparse.Namespace) -> None:
    """Run the curation pipeline."""
    from pathlib import Path

    _load_env_creds()
    llm_key, llm_base = _env_agent_creds()

    output_dir = Path(args.output_dir)
    config_path = output_dir / "config.yaml"

    if config_path.exists() and args.stage:
        config = CurationConfig.load(config_path)
        if not config.api_key and llm_key:
            config.api_key = llm_key
        if not config.api_base_url and llm_base:
            config.api_base_url = llm_base
        if args.model is not None:
            config.model = args.model
        if getattr(args, "agent_kind", None) is not None:
            config.agent_kind = args.agent_kind
        if getattr(args, "codex_auth_mode", None) is not None:
            config.codex_auth_mode = args.codex_auth_mode
        if getattr(args, "codex_sandbox_mode", None) is not None:
            config.codex_sandbox_mode = args.codex_sandbox_mode
        if getattr(args, "codex_timeout_seconds", None) is not None:
            config.codex_timeout_seconds = args.codex_timeout_seconds
        if getattr(args, "codex_network_access", None):
            config.codex_network_access = True
        if getattr(args, "codex_model_reasoning_effort", None) is not None:
            config.codex_model_reasoning_effort = args.codex_model_reasoning_effort
        if args.workflow:
            config.workflow = args.workflow
    else:
        if not args.source_dir:
            print("Error: source_dir is required for a new run", file=sys.stderr)
            sys.exit(1)
        lang = None
        if args.lang:
            lang = SourceLanguage(args.lang.lower())
        kwargs: dict = {
            "source_dir": str(Path(args.source_dir).resolve()),
            "source_subdir": getattr(args, "source_subdir", "") or "",
            "output_dir": str(output_dir.resolve()),
            "source_language": lang,
            "workflow": args.workflow or "verified_to_lean",
        }
        if args.model is not None:
            kwargs["model"] = args.model
        if getattr(args, "agent_kind", None) is not None:
            kwargs["agent_kind"] = args.agent_kind
        if getattr(args, "codex_auth_mode", None) is not None:
            kwargs["codex_auth_mode"] = args.codex_auth_mode
        if getattr(args, "codex_sandbox_mode", None) is not None:
            kwargs["codex_sandbox_mode"] = args.codex_sandbox_mode
        if getattr(args, "codex_timeout_seconds", None) is not None:
            kwargs["codex_timeout_seconds"] = args.codex_timeout_seconds
        if getattr(args, "codex_network_access", None):
            kwargs["codex_network_access"] = True
        if getattr(args, "codex_model_reasoning_effort", None) is not None:
            kwargs["codex_model_reasoning_effort"] = args.codex_model_reasoning_effort
        # Pull credentials + base URL from env so the curation agent can talk
        # to the configured LiteLLM proxy (or Anthropic direct). Order: explicit
        # `LLM_API_*` (the .env's litellm-style names), then Anthropic-direct
        # fallbacks. Both empty → agent fails at first call (user fixes .env).
        if llm_key:
            kwargs["api_key"] = llm_key
        if llm_base:
            kwargs["api_base_url"] = llm_base
        config = CurationConfig(**kwargs)

    if (
        config.agent_kind == "codex"
        and args.model is None
        and config.model.startswith("claude-")
    ):
        config.model = ""

    if getattr(args, "no_orchestrator", False):
        config.use_orchestrator = False
    if getattr(args, "max_concurrent", None) is not None:
        config.max_concurrent_executors = args.max_concurrent
    llm_review_override = getattr(args, "llm_review", None)
    if getattr(args, "llm_review_check", None):
        if llm_review_override is None:
            config.validate_llm_review = True
        config.validate_llm_review_checks = args.llm_review_check
    if getattr(args, "llm_review_memory", None):
        if llm_review_override is None:
            config.validate_llm_review = True
        config.validate_llm_review_memory_path = str(
            Path(args.llm_review_memory).resolve()
        )
    if getattr(args, "llm_review_checks_file", None):
        if llm_review_override is None:
            config.validate_llm_review = True
        config.validate_llm_review_checks_path = str(
            Path(args.llm_review_checks_file).resolve()
        )
    if llm_review_override is not None:
        config.validate_llm_review = llm_review_override

    if args.max_turns and args.stage:
        field = f"max_turns_{args.stage}"
        if hasattr(config, field):
            setattr(config, field, args.max_turns)

    _redact_local_codex_credentials(config)

    pipeline = get_pipeline(config)
    start_from = args.stage if args.stage else None

    async def _run():
        results = await pipeline.run(
            start_from=start_from,
            force=args.force,
            continue_session=getattr(args, "continue_session", False),
        )
        for r in results:
            if not r.success:
                sys.exit(1)

    anyio.run(_run)


def cmd_status(args: argparse.Namespace) -> None:
    """Show pipeline status."""
    from pathlib import Path

    output_dir = Path(args.output_dir)
    config_path = output_dir / "config.yaml"
    if not config_path.exists():
        print(f"No pipeline found at {output_dir}", file=sys.stderr)
        sys.exit(1)

    config = CurationConfig.load(config_path)
    pipeline = get_pipeline(config)
    status = pipeline.status()

    print(f"Pipeline: {output_dir}")
    print(f"Source: {config.source_dir}")
    print(f"Language: {config.source_language}")
    print(f"Workflow: {config.workflow}")
    print(f"Agent: {config.agent_kind}")
    print(f"Model: {config.model}")
    print()
    for stage_name, state in status.items():
        marker = "+" if state == "completed" else " "
        print(f"  [{marker}] {stage_name}")


def cmd_python_from_json(args: argparse.Namespace) -> None:
    """Scaffold a Lean 4 benchmark from a pre-curated ``benchmark.json``.

    Usage: ``python -m vero.curation python-from-json <benchmark.json> <out_dir>``.
    """
    from pathlib import Path

    from vero.curation.stages.python_from_json import run_python_from_json

    bench_json = Path(args.benchmark_json).resolve()
    out_dir = Path(args.out_dir).resolve()

    if not bench_json.exists():
        print(f"Error: benchmark.json not found at {bench_json}", file=sys.stderr)
        sys.exit(1)

    plan = run_python_from_json(bench_json, out_dir, lean_version=args.lean_version)
    print(f"Scaffolded Lean benchmark for '{plan.benchmark_id}' at {out_dir}")
    print(f"  package:     {plan.package}")
    print(f"  modules:     {', '.join(fs.module for fs in plan.files)}")
    total_apis = sum(len(fs.apis) for fs in plan.files)
    print(f"  apis:        {total_apis}")
    if plan.warnings:
        print("  warnings:")
        for w in plan.warnings:
            print(f"    - {w}")


def cmd_extract(args: argparse.Namespace) -> None:
    """Extract task index from a completed Lean project."""
    from pathlib import Path

    from vero.curation.marker import count_metrics, extract_tasks_from_project

    project_dir = Path(args.project_dir)
    if not project_dir.exists():
        print(f"Directory not found: {project_dir}", file=sys.stderr)
        sys.exit(1)

    tasks = extract_tasks_from_project(project_dir)
    metrics = count_metrics(project_dir)

    print(f"Project: {project_dir}")
    print(f"Metrics: {json.dumps(metrics, indent=2)}")
    print(f"\nBenchmark tasks ({len(tasks)}):")
    for t in tasks:
        sorry = " (sorry)" if t.is_sorry else ""
        print(f"  {t.key:12s} {t.api:30s} {t.file}:{t.line}{sorry}")


def cmd_promote_memory(args: argparse.Namespace) -> None:
    """Promote checked validation memory candidates into durable memory."""
    from pathlib import Path

    count = promote_memory_candidates(
        Path(args.candidates_md).resolve(),
        Path(args.memory_md).resolve(),
    )
    print(f"Promoted {count} validation memory candidate(s).")


def main() -> None:
    parser = argparse.ArgumentParser(
        prog="vero.curation",
        description="Curation Pipeline — Verified Code to Lean 4 Benchmarks",
    )
    sub = parser.add_subparsers(dest="command", required=True)

    # run
    p_run = sub.add_parser("run", help="Run the curation pipeline")
    p_run.add_argument("source_dir", nargs="?", help="Path to source repository")
    p_run.add_argument("output_dir", help="Path to output workspace")
    p_run.add_argument(
        "--lang",
        choices=["dafny", "verus", "coq", "python", "lean"],
        help="Source language (auto-detected if omitted)",
    )
    p_run.add_argument(
        "--source-subdir",
        default="",
        help="Subdirectory within repo where source code lives",
    )
    p_run.add_argument("--workflow", choices=list(WORKFLOWS), help="Pipeline workflow")
    p_run.add_argument("--stage", help="Start from this stage (by name)")
    p_run.add_argument("--force", action="store_true", help="Force re-run of stages")
    p_run.add_argument(
        "--continue",
        dest="continue_session",
        action="store_true",
        help="Resume the agent session from where it stopped",
    )
    p_run.add_argument(
        "--model",
        default=None,
        help="Agent model to use (default: CurationConfig default; Codex local may omit)",
    )
    p_run.add_argument(
        "--agent-kind",
        choices=["claude", "codex"],
        default=None,
        help="Agent backend for curation stages",
    )
    p_run.add_argument(
        "--codex-auth-mode",
        choices=["api", "local"],
        default=None,
        help="Codex auth mode: api uses configured API key; local uses ~/.codex login",
    )
    p_run.add_argument(
        "--codex-sandbox-mode",
        choices=["workspace-write", "read-only", "danger-full-access"],
        default=None,
        help="Sandbox mode passed to codex exec",
    )
    p_run.add_argument(
        "--codex-timeout-seconds",
        type=int,
        default=None,
        help="Timeout for each codex exec agent call",
    )
    p_run.add_argument(
        "--codex-network-access",
        action="store_true",
        help="Allow network access for Codex workspace-write sandbox",
    )
    p_run.add_argument(
        "--codex-model-reasoning-effort",
        choices=["low", "medium", "high", "xhigh"],
        default=None,
        help="Set Codex model_reasoning_effort for curation agent calls",
    )
    p_run.add_argument(
        "--max-turns", type=int, help="Override max turns for the target stage"
    )
    p_run.add_argument(
        "--no-orchestrator",
        action="store_true",
        help="Disable orchestrated translate (use single-agent fallback)",
    )
    p_run.add_argument(
        "--max-concurrent",
        type=int,
        default=None,
        help="Max concurrent executor agents (orchestrated translate)",
    )
    llm_review_group = p_run.add_mutually_exclusive_group()
    llm_review_group.add_argument(
        "--llm-review",
        dest="llm_review",
        action="store_true",
        default=None,
        help="Enable opt-in LLM review during the validate stage",
    )
    llm_review_group.add_argument(
        "--no-llm-review",
        dest="llm_review",
        action="store_false",
        help="Disable validate-stage LLM review in the saved config",
    )
    p_run.add_argument(
        "--llm-review-check",
        action="append",
        help=(
            "Run only this LLM-review check during validate; repeat to select "
            "multiple checks. Built-ins: "
            + ", ".join(LLM_REVIEW_CHECKS)
            + ". Custom names require --llm-review-checks-file."
        ),
    )
    p_run.add_argument(
        "--llm-review-memory",
        help="Path to validation memory markdown to pass into LLM review",
    )
    p_run.add_argument(
        "--llm-review-checks-file",
        help=(
            "YAML/JSON file with additional LLM-review checks. Shape: "
            "`checks: [{name, description, prompt}]`."
        ),
    )

    # status
    p_status = sub.add_parser("status", help="Show pipeline status")
    p_status.add_argument("output_dir", help="Path to output workspace")

    # extract
    p_extract = sub.add_parser("extract", help="Extract task index from Lean project")
    p_extract.add_argument("project_dir", help="Path to Lean project directory")

    # promote-memory
    p_promote = sub.add_parser(
        "promote-memory",
        help="Promote checked validate/memory_candidates.md lines into memory",
    )
    p_promote.add_argument("candidates_md", help="Path to memory_candidates.md")
    p_promote.add_argument("memory_md", help="Path to durable validation memory")

    # python-from-json
    p_pfj = sub.add_parser(
        "python-from-json",
        help=(
            "Scaffold a Lean 4 benchmark from a pre-curated Python benchmark.json "
            "(mode A of the Python workflow)."
        ),
    )
    p_pfj.add_argument(
        "benchmark_json",
        help="Path to benchmark.json (e.g. path/to/benchmark.json)",
    )
    p_pfj.add_argument(
        "out_dir",
        help="Output directory (the Lean benchmark root, e.g. curation_outputs/primepy/)",
    )
    p_pfj.add_argument(
        "--lean-version",
        default="4.29.1",
        help="Lean toolchain version (default: 4.29.1)",
    )

    args = parser.parse_args()

    if args.command == "run":
        cmd_run(args)
    elif args.command == "status":
        cmd_status(args)
    elif args.command == "extract":
        cmd_extract(args)
    elif args.command == "promote-memory":
        cmd_promote_memory(args)
    elif args.command == "python-from-json":
        cmd_python_from_json(args)


if __name__ == "__main__":
    main()
