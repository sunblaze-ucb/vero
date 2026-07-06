"""Per-mode ``INSTRUCTION.md`` rendering for the agent.

The instruction file is the agent's single source of truth inside the sandbox. It tells the agent:

- Why the benchmark exists (what's being measured).
- What the sandbox looks like (layout, frozen vs editable).
- The exact marker grammar and hard rules.
- The per-mode task.
- How it will be graded (success criteria + grading states + anti-cheat).
- Practical workflow advice (oracle commands, budgeting across specs).

Per-mode templates live under ``templates/instruction/`` (Jinja2): ``proof.md.j2`` and ``codeproof.md.j2`` each extend ``base.md.j2`` and override the ``mode_body`` block. This module just picks the template by mode and hands over the render context.

Consumed by :class:`vero.generation.agents.base.Agent` implementations via ``create_sandbox`` → ``render_instruction``.
"""

from __future__ import annotations

from functools import lru_cache
from pathlib import Path
from typing import Literal

from jinja2 import Environment, FileSystemLoader, StrictUndefined, select_autoescape

from vero.generation.benchmark import Benchmark

Mode = Literal["proof", "codeproof"]


def _find_repo_root() -> Path:
    """Walk up from this file until we find the repo's ``templates/`` dir."""
    cur = Path(__file__).resolve()
    for _ in range(10):
        cur = cur.parent
        if (cur / "templates").is_dir():
            return cur
    raise FileNotFoundError("Could not locate repo root with a `templates/` directory")


REPO_ROOT = _find_repo_root()
TEMPLATES_DIR = REPO_ROOT / "templates"


@lru_cache(maxsize=1)
def _env() -> Environment:
    return Environment(
        loader=FileSystemLoader(TEMPLATES_DIR),
        autoescape=select_autoescape(disabled_extensions=("md", "j2"), default=False),
        undefined=StrictUndefined,
        keep_trailing_newline=True,
        trim_blocks=False,
        lstrip_blocks=False,
    )


def render_instruction(
    bench: Benchmark,
    *,
    mode: Mode,
    previous_feedback: str | None = None,
    iteration_index: int = 0,
    iteration_total: int = 1,
    chunk_minutes: float | None = None,
    upstream_source: bool = False,
) -> str:
    n_packages = len(bench.packages)
    n_modules = sum(len(p.modules) for p in bench.packages)
    n_specs = sum(len(m.specs) for m in bench.iter_modules())
    n_apis = sum(len(m.apis) for m in bench.iter_modules())
    modules_list = ", ".join(m.name for m in bench.iter_modules())

    packages = [
        {
            "name": p.name,
            "bundle_type": p.bundle_type,
            "repo_impl_field": p.repo_impl_field,
            "modules": [m.name for m in p.modules],
        }
        for p in bench.packages
    ]

    part_a_advice = (
        "No action on ``Impl/*.lean`` — reference impls are in place and "
        "``canonical`` points at them."
        if mode == "proof"
        else (
            "Fill every ``!benchmark code def=<fn>`` slot in ``Impl/*.lean`` "
            "with a simple, correct implementation. Run ``lake build`` to "
            "confirm ``Test.lean`` passes before moving to proofs."
        )
    )

    template = _env().get_template(f"instruction/{mode}.md.j2")
    return template.render(
        project=bench.root_package,
        packages=packages,
        n_packages=n_packages,
        mode=mode,
        n_modules=n_modules,
        n_specs=n_specs,
        n_apis=n_apis,
        modules_list=modules_list,
        part_a_advice=part_a_advice,
        previous_feedback=previous_feedback,
        iteration_index=iteration_index,
        iteration_total=iteration_total,
        chunk_minutes=(round(chunk_minutes, 1) if chunk_minutes is not None else None),
        upstream_source=upstream_source,
    )
