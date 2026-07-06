"""Sandbox builder — copy benchmark + materialize ``Proof/`` + strip curation.

Given a benchmark in the ratified bundle paradigm, produce a sandbox the agent can freely edit:

1. ``shutil.copytree`` the benchmark into the sandbox dir (minus lake caches),
   then reuse the benchmark's ``.lake/packages`` dependency cache when present.
2. Materialize per-mode ``<Package>/Proof/<Module>.lean`` via :mod:`vero.generation.proof_materialize`. In ``codeproof`` mode, also materialize the dormant ``<Package>/Proof/Joint.lean`` slot.
3. **Codeproof only**: overwrite every ``!benchmark code`` slot in ``Impl/*.lean`` with a single ``sorry`` line. The LLM fills the implementation itself. In ``proof`` mode the reference impl stays (``canonical`` is given).
4. Strip ``!curation @…`` single-line annotations from every sandbox file the agent can touch. Keep marker + non-marker content otherwise verbatim.
5. Write ``INSTRUCTION.md`` at the sandbox root — consumed by the agent runner.

The sandbox is self-contained: per-module ``lake build`` / ``lake lean`` invocations on each ``<Package>/Proof/<Module>.lean`` file are the evaluator's oracle. There is no aggregator file; the evaluator compiles each proof module independently so one failing module doesn't cascade through the whole benchmark.
"""

from __future__ import annotations

import os
import shutil
import subprocess
from dataclasses import dataclass
from pathlib import Path
from typing import TYPE_CHECKING, Literal

from loguru import logger

if TYPE_CHECKING:
    from vero.generation.extractor import Artifact

from vero.generation.benchmark import (
    Benchmark,
    load_slots,
    proof_editable_files,
)
from vero.generation.proof_materialize import materialize_proof

Mode = Literal["proof", "codeproof"]


@dataclass
class SandboxResult:
    sandbox_dir: Path
    mode: Mode
    proof_files: tuple[Path, ...]
    instruction_file: Path


# ─── Public API ─────────────────────────────────────────────────


def create_sandbox(
    benchmark_dir: Path,
    sandbox_dir: Path,
    *,
    mode: Mode,
    overwrite: bool = False,
    strip_manifest: bool = True,
    previous_feedback: str | None = None,
    iteration_index: int = 0,
    iteration_total: int = 1,
    seed_artifact: "Artifact | None" = None,
    chunk_minutes: float | None = None,
    source_context: str = "lean",
) -> SandboxResult:
    """Build a ready-to-edit sandbox for ``benchmark_dir`` under ``sandbox_dir``.

    Parameters
    ----------
    benchmark_dir:
        Path to the curation-stage benchmark (contains ``manifest.json``).
    sandbox_dir:
        Target directory. Must not exist unless ``overwrite=True``.
    mode:
        Evaluation mode. Controls what ``Proof/`` is materialized, whether ``Impl/*`` code slots are ``sorry``'d, and which instructions go into ``INSTRUCTION.md``.
    strip_manifest:
        Delete ``manifest.json`` from the sandbox once setup finishes. The agent does not need it and it is not part of the Lean build; the evaluator re-creates a fresh sandbox from the source ``benchmark_dir`` so no downstream pipeline step reads the sandbox's manifest. Set ``False`` if you need it (e.g. debugging).
    previous_feedback:
        When set (typically by the iteration harness), rendered INSTRUCTION gains a "Previous iteration feedback" block citing the prior eval's ``report.md``. Pair with ``iteration_index`` / ``iteration_total`` for the iteration counter. A copy of the feedback is also written to ``FEEDBACK.md`` at the sandbox root.
    iteration_index:
        0-based iteration number for display in the INSTRUCTION. Only consulted when ``previous_feedback`` is set.
    iteration_total:
        Total iterations planned (max + 1). Only consulted when ``previous_feedback`` is set.
    seed_artifact:
        RESUME support. When set (typically the prior trial's ``artifact.json`` loaded via ``read_artifact``), the fresh sandbox's filled-slot bodies are overlaid from it *after* materialization — so the agent continues from the previous trial's proofs/impls rather than restarting from blank stubs. Slots are matched by ``(prefix, key, def_name)``, never by line number; only ``found`` slots with a non-empty body are applied. ``None`` (default) ⇒ blank stubs (original behavior).
    """
    benchmark_dir = Path(benchmark_dir).resolve()
    sandbox_dir = Path(sandbox_dir).resolve()

    if sandbox_dir.exists():
        if not overwrite:
            raise FileExistsError(
                f"sandbox {sandbox_dir} exists; pass overwrite=True to replace."
            )
        shutil.rmtree(sandbox_dir)

    _copy_benchmark(benchmark_dir, sandbox_dir)
    _link_lake_packages(benchmark_dir, sandbox_dir)
    _ensure_mathlib_cache(sandbox_dir)

    # Load manifest from the *sandbox* copy from here on so all edits are local.
    bench = Benchmark(sandbox_dir)

    # Drop sidecar illustrations — they're not imported and only confuse agents.
    for dirname in (
        f"{bench.root_package}/Proof_modeproof",
        f"{bench.root_package}/Proof_modecodeproof",
    ):
        side = sandbox_dir / dirname
        if side.is_dir():
            shutil.rmtree(side)

    # Materialize Proof/ into the sandbox per mode.
    materialize_proof(sandbox_dir, mode=mode)

    # Blank out code slots in codeproof mode. The agent must WRITE the impl,
    # so it also gets EMPTY `code_aux` / `global_aux` slots (curator helpers
    # removed) — otherwise the reference algorithm leaks via the helpers while
    # only the API body is `sorry`'d. `code def=` bodies become `sorry` (a def
    # body placeholder); the aux slots are EMPTIED (blank interior, not `sorry`
    # — they hold whole `def`s, and `sorry` at declaration position won't
    # parse). All three keys are already declared agent-editable, so the agent
    # re-supplies whatever helpers it needs. Specs never import Impl (they go
    # through Harness→Bundle), so emptying Impl aux does not touch any spec.
    if mode == "codeproof":
        for impl in bench.all_impl_files():
            _sorry_out_slots(impl, key="code")
            _empty_slots(impl, key="code_aux")
            _empty_slots(impl, key="global_aux")

    # Strip curation annotations from everything the agent can touch.
    editable = set(bench.all_impl_files()) | set(proof_editable_files(bench, mode))
    for f in editable:
        if f.exists():
            _strip_curation_lines(f)

    # RESUME: overlay a prior trial's filled slot bodies onto the fresh stubs
    # so the agent continues rather than restarts. Matched by identity, applied
    # after materialization + code-blanking so seeds win over the blank stubs.
    if seed_artifact is not None:
        from vero.generation.render import overlay_artifact_slots  # lazy: cycle

        if seed_artifact.mode != mode:
            raise ValueError(
                f"seed_artifact mode {seed_artifact.mode!r} != sandbox mode {mode!r}"
            )
        n = overlay_artifact_slots(sandbox_dir, seed_artifact)
        logger.info("resume: seeded {} filled slot(s) from prior artifact", n)

    # Drop any feedback copy from prior iterations. If the caller
    # provided ``previous_feedback``, land a fresh copy at the sandbox
    # root so the agent can open the file directly.
    feedback_file = sandbox_dir / "FEEDBACK.md"
    if feedback_file.exists():
        feedback_file.unlink()
    if previous_feedback is not None:
        feedback_file.write_text(previous_feedback, encoding="utf-8")

    # source_context=full: ship the prefetched upstream source into the sandbox
    # as agent reference material. Copied from the SOURCE benchmark's
    # ``upstream_source/`` (excluded from the benchmark copytree above, so it
    # only appears here in full mode — never in the grading re-render/artifact).
    has_upstream = False
    if source_context == "full":
        has_upstream = _ship_upstream_source(benchmark_dir, sandbox_dir)

    # Instructions.
    instr = sandbox_dir / "INSTRUCTION.md"
    from vero.generation.prompt import render_instruction  # lazy: avoids cycle

    instr.write_text(
        render_instruction(
            bench,
            mode=mode,
            previous_feedback=previous_feedback,
            iteration_index=iteration_index,
            iteration_total=iteration_total,
            chunk_minutes=chunk_minutes,
            upstream_source=has_upstream,
        ),
        encoding="utf-8",
    )

    # Drop manifest.json from the agent-visible sandbox.
    if strip_manifest:
        manifest = sandbox_dir / "manifest.json"
        if manifest.exists():
            manifest.unlink()

    return SandboxResult(
        sandbox_dir=sandbox_dir,
        mode=mode,
        proof_files=tuple(proof_editable_files(bench, mode)),
        instruction_file=instr,
    )


# ─── Internals ──────────────────────────────────────────────────


def _copy_benchmark(src: Path, dst: Path) -> None:
    """Recursive copy, skipping lake caches + hidden scratch dirs."""

    def ignore(dir: str, names: list[str]) -> list[str]:
        out: list[str] = []
        for n in names:
            if n in {".lake", "build", ".git", "__pycache__", "upstream_source"}:
                # ``upstream_source`` holds prefetched upstream Python for
                # source_context=full — it is AGENT CONTEXT ONLY. Never copy it
                # via the benchmark copytree (that render also backs grading +
                # the extracted artifact); it is added separately, only in full
                # mode, by ``_ship_upstream_source``.
                out.append(n)
        return out

    shutil.copytree(src, dst, ignore=ignore)


def _ship_upstream_source(benchmark_dir: Path, sandbox_dir: Path) -> bool:
    """Copy the benchmark's prefetched ``upstream_source/`` into the sandbox
    (source_context=full). Returns True if any upstream file was shipped.

    The upstream Python is AGENT REFERENCE CONTEXT ONLY: it is copied here (not
    via the benchmark copytree), so it never reaches the grading re-render or
    the extracted artifact. ``PROVENANCE.txt`` is copied too so the agent can
    see the exact url@sha. If the source benchmark has no ``upstream_source/``
    (prefetch not run), this is a no-op returning False — the instruction then
    simply omits the reference note.
    """
    src = benchmark_dir / "upstream_source"
    if not src.is_dir():
        logger.warning(
            "source_context=full but {} is missing — run scripts/prefetch_upstream.py",
            src,
        )
        return False
    files = [p for p in src.rglob("*") if p.is_file()]
    if not files:
        return False
    dst = sandbox_dir / "upstream_source"
    shutil.copytree(src, dst, dirs_exist_ok=True)
    logger.info(
        "source_context=full: shipped {} upstream file(s) → {}", len(files), dst
    )
    return True


_WRITABLE_LAKE_PACKAGES = {"proofwidgets"}


def _mathlib_olean_count(sandbox_dir: Path) -> int:
    """Number of built mathlib ``.olean`` files reachable from the sandbox.

    Follows the symlinked ``.lake/packages/mathlib`` into the shared benchmark
    cache. Zero means mathlib would have to be recompiled from source.
    """
    build_lib = (
        sandbox_dir / ".lake" / "packages" / "mathlib" / ".lake" / "build" / "lib"
    )
    if not build_lib.exists():
        return 0
    # Count is cheap enough; cap the walk by bailing once we clearly have a cache.
    n = 0
    for _ in build_lib.rglob("*.olean"):
        n += 1
        if n >= 100:  # any real mathlib cache has thousands; 100 is proof-of-life
            return n
    return n


def _ensure_mathlib_cache(sandbox_dir: Path) -> None:
    """Populate the mathlib olean cache when the sandbox needs mathlib but has none.

    A benchmark that ``require``s mathlib but ships no built ``.olean`` cache
    forces every grade sandbox to recompile all ~5000 mathlib modules — which
    blows past the grader's Stage-1 build timeout (600s) and yields a false
    ``impl_broken`` 0-score, and also triggers read-only-FS write errors when
    lake tries to write oleans into the shared (symlinked) cache. Running
    ``lake exe cache get`` fetches pre-built oleans from the global
    ``~/.cache/mathlib`` store in seconds, so grading only *reads* mathlib.

    No-op unless the project requires mathlib AND the cache is unpopulated, so
    warm benchmarks (flocq, dedekind_reals) pay nothing. Best-effort: a failure
    (offline, no global cache) is logged and left to the build to surface.
    """
    lakefiles = list(sandbox_dir.glob("lakefile.*"))
    requires_mathlib = any(
        "mathlib" in lf.read_text(encoding="utf-8", errors="ignore").lower()
        for lf in lakefiles
    )
    if not requires_mathlib:
        return
    if _mathlib_olean_count(sandbox_dir) >= 100:
        return  # cache already warm (symlinked benchmark cache is populated)

    logger.info(
        "sandbox needs mathlib but cache is empty — running `lake exe cache get`"
    )
    env = {
        **os.environ,
        "PATH": f"{Path.home() / '.elan' / 'bin'}:{os.environ.get('PATH', '')}",
    }
    for stage in (["lake", "update"], ["lake", "exe", "cache", "get"]):
        try:
            r = subprocess.run(
                stage,
                cwd=str(sandbox_dir),
                env=env,
                capture_output=True,
                text=True,
                timeout=900,
            )
            if r.returncode != 0:
                logger.warning(
                    "sandbox `{}` exit={} (mathlib cache best-effort): {}",
                    " ".join(stage),
                    r.returncode,
                    (r.stderr or r.stdout or "")[-300:],
                )
        except (subprocess.TimeoutExpired, OSError) as e:
            logger.warning("sandbox `{}` failed: {}", " ".join(stage), e)
    logger.info(
        "sandbox mathlib cache now has ~{} oleans", _mathlib_olean_count(sandbox_dir)
    )


def _link_lake_packages(src: Path, dst: Path) -> None:
    """Reuse Lake dependency packages without copying multi-GB caches.

    The sandbox gets a fresh project build directory, but Lake can resolve
    mathlib and inherited package sources from the benchmark's existing cache.
    This avoids forcing proof agents to clone dependencies from network-disabled
    sandboxes. A few small Lake packages generate files in their own package
    directory when extra imports are used; copy those packages so agent sandboxes
    can write the generated files without mutating the benchmark cache.
    """

    packages = src / ".lake" / "packages"
    if not packages.is_dir():
        return

    lake_dir = dst / ".lake"
    lake_dir.mkdir(parents=True, exist_ok=True)
    target = lake_dir / "packages"
    if target.exists() or target.is_symlink():
        return
    target.mkdir()

    for package in packages.iterdir():
        package_target = target / package.name
        if package.name in _WRITABLE_LAKE_PACKAGES:
            shutil.copytree(package, package_target, symlinks=True)
        else:
            package_target.symlink_to(
                package.resolve(), target_is_directory=package.is_dir()
            )


def _sorry_out_slots(file: Path, *, key: str) -> None:
    """Replace interiors of every ``!benchmark key=…`` slot with a single ``  sorry``."""
    slots = [s for s in load_slots(file) if s.prefix == "benchmark" and s.key == key]
    if not slots:
        return
    # Apply replacements bottom-up so line numbers stay valid.
    lines = file.read_text().splitlines(keepends=True)
    for s in sorted(slots, key=lambda s: -s.start_line):
        start = s.start_line  # @start line index (1-based) = 0-based index
        end = s.end_line  # @end line index (1-based)
        # interior = lines[start .. end - 1] (0-based slice: [start, end-1))
        lines[start : end - 1] = ["  sorry\n"]
    file.write_text("".join(lines), encoding="utf-8")


def _empty_slots(file: Path, *, key: str) -> None:
    """Blank the interior of every ``!benchmark key=…`` slot — leave the
    marker lines, remove everything between them.

    Used for ``code_aux`` / ``global_aux`` in codeproof mode: those slots hold
    whole helper ``def``s (not proof bodies), so they are EMPTIED rather than
    ``sorry``'d (a bare ``sorry`` at declaration position would not parse). The
    agent re-supplies its own helpers in these (agent-editable) slots.
    """
    slots = [s for s in load_slots(file) if s.prefix == "benchmark" and s.key == key]
    if not slots:
        return
    lines = file.read_text().splitlines(keepends=True)
    # Bottom-up so earlier line indices stay valid.
    for s in sorted(slots, key=lambda s: -s.start_line):
        # interior = lines[start_line .. end_line - 1) (0-based); drop it.
        lines[s.start_line : s.end_line - 1] = []
    file.write_text("".join(lines), encoding="utf-8")


def _strip_curation_lines(file: Path) -> None:
    """Remove any line whose stripped form starts with ``-- !curation``."""
    lines = file.read_text().splitlines(keepends=True)
    kept = [ln for ln in lines if not ln.lstrip().startswith("-- !curation")]
    if len(kept) != len(lines):
        file.write_text("".join(kept), encoding="utf-8")
