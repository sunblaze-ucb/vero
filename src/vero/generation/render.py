"""Render a fresh benchmark sandbox from an ``Artifact``.

Used by the evaluator to run grading against a **clean**, freshly materialized copy of the benchmark with ONLY the agent's marker-slot edits applied. Anything the agent did outside the expected slot schedule (modifying frozen files, adding stray definitions, touching ``manifest.json`` or ``lakefile.toml``) is dropped on the floor — the frozen pieces come from the source benchmark dir, not from the agent's working sandbox.

This gives evaluation three guarantees:

1. **Determinism** — for a given ``(benchmark_dir, artifact, mode)`` triple, the resulting sandbox is byte-identical.
2. **Anti-cheat on frozen files** — the agent cannot smuggle a ``spec_X := True.intro`` patch through.
3. **Anti-cheat on extra markers** — ``artifact.extras`` are never rendered; only slots in the expected schedule contribute.
"""

from __future__ import annotations

from pathlib import Path
from typing import Literal

from loguru import logger

from vero.generation.benchmark import Benchmark, load_slots
from vero.generation.extractor import Artifact, ExtractedSlot
from vero.generation.sandbox import SandboxResult, create_sandbox

Mode = Literal["proof", "codeproof"]


def overlay_artifact_slots(sandbox_dir: Path, artifact: Artifact) -> int:
    """Overlay an artifact's filled slot bodies onto an existing sandbox.

    Edits the marker regions of files already present under ``sandbox_dir``
    in place; does NOT create the sandbox (the caller owns that). Slots are
    matched by ``(prefix, key, def_name)`` — never by line number — so the
    fresh sandbox's own marker positions govern. Only ``found`` slots with a
    non-empty ``body_lines`` are applied. Returns the count applied.

    Shared by :func:`render_sandbox` (evaluator's clean re-render) and by
    ``create_sandbox(seed_artifact=…)`` (the resume path — a new trial
    continues from a prior trial's filled slots).
    """
    sandbox_dir = Path(sandbox_dir)
    by_file: dict[str, list[ExtractedSlot]] = {}
    for s in artifact.slots:
        if not s.found:
            continue
        # Pure comments with no real body are effectively identical to the
        # materialize-time default; skip re-rendering so we don't touch the
        # file unnecessarily.
        if not s.body_lines:
            continue
        by_file.setdefault(s.file, []).append(s)

    filled = 0
    for file_rel, slots in by_file.items():
        path = sandbox_dir / file_rel
        if not path.exists():
            logger.warning(
                "artifact references {} which is not in the materialized sandbox",
                file_rel,
            )
            continue
        # Parse the fresh file's marker positions (they may differ from the
        # artifact's line numbers, so we resolve by (prefix, key, def_name)).
        parsed = {(p.prefix, p.key, p.def_name): p for p in load_slots(path)}
        lines = path.read_text().splitlines(keepends=True)

        # Apply bottom-up so earlier line numbers stay valid.
        pending: list[tuple[int, int, list[str]]] = []
        for s in slots:
            key = (s.prefix, s.key, s.def_name)
            target = parsed.get(key)
            if target is None:
                logger.warning(
                    "slot {}/{}/{} in artifact has no matching marker in fresh "
                    "sandbox file {} — skipping",
                    s.prefix,
                    s.key,
                    s.def_name,
                    file_rel,
                )
                continue
            pending.append((target.start_line, target.end_line, s.body_lines))
            filled += 1
        pending.sort(key=lambda t: -t[0])
        for start_line, end_line, body in pending:
            new_body = [ln if ln.endswith("\n") else ln + "\n" for ln in body]
            # interior occupies lines[start_line : end_line - 1] (0-indexed).
            lines[start_line : end_line - 1] = new_body
        path.write_text("".join(lines), encoding="utf-8")
    return filled


def render_sandbox(
    benchmark_dir: Path,
    artifact: Artifact,
    target_dir: Path,
    *,
    mode: Mode,
    overwrite: bool = True,
) -> SandboxResult:
    """Materialize a fresh sandbox + overlay the artifact's slot bodies.

    Parameters
    ----------
    benchmark_dir:
        Source benchmark (contains ``manifest.json``). Frozen files come
        from here.
    artifact:
        Artifact produced by ``extract()``. Any slot with ``found=True``
        overlays its ``body_lines`` into the fresh sandbox.
    target_dir:
        Where the fresh sandbox is rebuilt. Must not exist unless
        ``overwrite=True``.
    mode:
        Evaluation mode; controls which slots the pipeline plants.
    """
    if artifact.mode != mode:
        raise ValueError(f"artifact mode {artifact.mode!r} != requested mode {mode!r}")

    # strip_manifest=False keeps ``manifest.json`` in the eval sandbox so
    # downstream evaluator steps (``Benchmark(eval_sandbox_dir)``,
    # joint_rerender) can load it. This sandbox is never shown to the agent.
    sandbox = create_sandbox(
        benchmark_dir,
        target_dir,
        mode=mode,
        overwrite=overwrite,
        strip_manifest=False,
    )
    bench = Benchmark(sandbox.sandbox_dir)

    filled = overlay_artifact_slots(sandbox.sandbox_dir, artifact)

    # Sanity: every non-default slot from the artifact should have landed.
    logger.info(
        "rendered {} / {} editable slots from artifact into {}",
        filled,
        sum(1 for s in artifact.slots if s.found and s.body_lines),
        sandbox.sandbox_dir,
    )
    # Fully ignored: artifact.extras (by design).
    if artifact.extras:
        logger.info(
            "dropped {} extra agent-added marker slot(s) during render "
            "(anti-cheat — extras never reach the evaluator)",
            len(artifact.extras),
        )

    # Return the base SandboxResult — the evaluator only needs its paths.
    # ``Benchmark(sandbox.sandbox_dir)`` will happily re-parse the filled file.
    _ = bench  # we already validated; keep a reference so linters don't nag
    return sandbox
