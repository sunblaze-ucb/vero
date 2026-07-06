"""CLI dispatcher for orchestrator tools.

The orchestrator agent calls these via Bash commands:

    python -m vero.curation.orchestrator.dispatch \\
        --workspace /path/to/workspace \\
        <command> [args...]

Each command reads/writes state from the workspace directory and
prints JSON to stdout for the orchestrator to consume.
"""

from __future__ import annotations

import argparse
import json

import anyio


def main() -> None:
    parser = argparse.ArgumentParser(
        prog="vero.curation.orchestrator.dispatch",
        description="Orchestrator tool dispatcher",
    )
    parser.add_argument(
        "--workspace",
        required=True,
        help="Path to the curation workspace directory",
    )

    sub = parser.add_subparsers(dest="command", required=True)

    # analyze_plan
    sub.add_parser("analyze_plan", help="Parse plan.json into modules and layers")

    # dispatch_executor
    p_exec = sub.add_parser("dispatch_executor", help="Run executor for one module")
    p_exec.add_argument("--module", required=True, help="Module name")
    p_exec.add_argument(
        "--shared-context-file",
        default="",
        help="Path to file containing shared context text",
    )

    # dispatch_layer
    p_layer = sub.add_parser(
        "dispatch_layer", help="Run all executors for a layer in parallel"
    )
    p_layer.add_argument("--layer", type=int, required=True, help="Layer number")
    p_layer.add_argument(
        "--max-concurrent", type=int, default=4, help="Max concurrent executors"
    )

    # get_progress
    sub.add_parser("get_progress", help="Return current orchestration progress")

    # get_result
    p_result = sub.add_parser("get_result", help="Get result for a specific module")
    p_result.add_argument("--module", required=True, help="Module name")

    # run_build
    sub.add_parser("run_build", help="Run lake build on the project")

    # validate_markers
    sub.add_parser("validate_markers", help="Validate markers across all files")

    args = parser.parse_args()

    from pathlib import Path

    from vero.curation.orchestrator import tools

    workspace = Path(args.workspace)

    if args.command == "analyze_plan":
        result = tools.analyze_plan(workspace)

    elif args.command == "dispatch_executor":
        shared_context = ""
        if args.shared_context_file:
            ctx_path = Path(args.shared_context_file)
            if ctx_path.exists():
                shared_context = ctx_path.read_text(encoding="utf-8")
        result = anyio.run(
            tools.dispatch_executor,
            workspace,
            args.module,
            shared_context,
        )

    elif args.command == "dispatch_layer":
        result = anyio.run(
            tools.dispatch_layer,
            workspace,
            args.layer,
            args.max_concurrent,
        )

    elif args.command == "get_progress":
        result = tools.get_progress(workspace)

    elif args.command == "get_result":
        result = tools.get_result(workspace, args.module)

    elif args.command == "run_build":
        result = anyio.run(tools.run_build, workspace)

    elif args.command == "validate_markers":
        result = tools.validate_all_markers(workspace)

    else:
        result = {"error": f"Unknown command: {args.command}"}

    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
