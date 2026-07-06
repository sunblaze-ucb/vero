"""Iteration harness — outer loop around ``dispatch_generation`` / ``dispatch_evaluation``.

Rationale: agents sometimes stop early, well under their turn/cost budget. When that happens the harness relaunches the agent on a fresh sandbox, optionally with the previous eval report attached as feedback, until the Done condition is met, a cumulative-cost cap is hit, or ``iterate.max`` retries are exhausted.

Layout (per run, when ``iterate.max > 0``):

.. code-block:: text

    <run_root>/
        run.yaml                 # frozen config (written before the loop starts)
        manifest.json            # one line per iteration's artifact, pointing at
                                 # the best iteration's source/artifact for back-compat
        iterations.json          # summary: per-iter build_ok / passed / cost / stop_reason
        iter-0/
            source/              # iteration 0's sandbox + artifact
            eval/<eval.name>/    # iteration 0's eval (when mode=eval)
        iter-1/ ...
        source/  → iter-<best>/source (copied for aggregator back-compat)
        eval/<eval.name>/ → iter-<best>/eval/<eval.name> (copied)

The "best" iteration is picked by ``passed_specs`` desc, tiebreak by lowest index.

When ``iterate.max == 0`` this module is never called — the CLI takes the single-shot codepath directly.
"""

from __future__ import annotations

import json
import shutil
import time
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Any

from loguru import logger
from omegaconf import DictConfig

# Dispatch functions are imported at module scope (not lazily inside
# ``_run_one_iteration``) so tests can patch them with
# ``patch.object(cli_iterate, "dispatch_generation", ...)``.
from vero.cli_dispatch import dispatch_evaluation, dispatch_generation


class _TransientStorm(RuntimeError):
    """Raised when a chunk exhausts its transient-error retries (sustained
    engine 404/overload). Propagates OUT of ``iterate_run`` so NO terminal
    marker is written — the external supervisor relaunches the eval later
    (resuming its in-place state) once the engine is healthy again."""


@dataclass
class IterationRecord:
    """One iteration's worth of summary state — what we write to
    ``iterations.json`` plus what the loop needs for stop conditions."""

    index: int
    source_dir: str
    artifact_path: str
    agent_ok: bool | None = None
    num_turns: int | None = None
    cost_usd: float | None = None
    eval_dir: str | None = None
    build_ok: bool | None = None
    passed_specs: int | None = None
    total_specs: int | None = None
    unfilled_specs: int | None = None
    failed_specs: int | None = None
    joint_passed: bool | None = None
    done: bool = False
    # Per-chunk performance-vs-time telemetry (populated by the loop).
    resumed_from: str | None = None  # prior chunk artifact this one seeded from
    usage: dict[str, int] | None = None  # tokens this chunk
    elapsed_seconds: float | None = None  # wall-clock this chunk (agent run)
    cumulative_seconds: float | None = None  # summed wall-clock through this chunk
    cumulative_cost_usd: float | None = None  # summed cost through this chunk
    killed_by_timeout: bool | None = (
        None  # True=hit chunk cutoff; False=agent exited on its own
    )
    # Two-axis position: which anti-laziness iteration + which checkpoint chunk.
    iteration: int | None = None
    chunk: int | None = None
    ended_by: str | None = None  # "timeout" | "gave_up" | "all_pass"
    build_seed_ok: bool | None = (
        None  # did THIS chunk's artifact build (drives resume seeding)
    )


@dataclass
class IterationSummary:
    """What ``iterate_run`` returns (mirrored to disk as
    ``iterations.json``)."""

    mode: str
    max: int
    stop_reason: str
    best_index: int | None
    iterations: list[IterationRecord] = field(default_factory=list)
    cumulative_cost_usd: float | None = None

    def to_json(self) -> str:
        data = {
            "mode": self.mode,
            "max": self.max,
            "stop_reason": self.stop_reason,
            "best_index": self.best_index,
            "cumulative_cost_usd": self.cumulative_cost_usd,
            "iterations": [asdict(r) for r in self.iterations],
        }
        return json.dumps(data, indent=2)


# ─── Public entry point ─────────────────────────────────────────────


def iterate_run(cfg: DictConfig, run_root: Path) -> IterationSummary:
    """Run up to ``iterate.max + 1`` full gen(+eval) iterations under
    ``run_root``. Write per-iteration output under ``iter-N/`` and a
    top-level ``iterations.json`` summary.
    """
    iter_cfg = cfg.iterate
    max_retries = int(iter_cfg.max)
    mode_label = str(iter_cfg.mode)
    stop_on_done = bool(iter_cfg.stop_on_done)
    budget_usd = iter_cfg.budget_usd
    budget_usd = float(budget_usd) if budget_usd is not None else None
    # iterate.feedback=false ⇒ blind iteration: per-iter eval still runs
    # (so passed_specs is recorded and stop_on_done can fire), but the
    # next sandbox does NOT receive the prior eval report (mode=eval) or
    # the self-assess nudge (mode=self).
    feedback_enabled = bool(iter_cfg.get("feedback", True))
    # RESUME: when true, each trial seeds its sandbox from the PRIOR trial's
    # artifact (filled proofs/impls carried forward) so the agent continues
    # rather than restarting from blank stubs. This is what turns N capped
    # trials into a single accumulating run — the basis for the
    # performance-vs-time curve (e.g. 6 × 30-min trials = up to 3h, each
    # picking up where the last left off).
    resume_enabled = bool(iter_cfg.get("resume", False))
    # Optional cumulative wall-clock cap across trials (seconds). None ⇒ only
    # the trial count (max+1) and budget bound the run.
    time_budget_s = iter_cfg.get("time_budget_seconds", None)
    time_budget_s = float(time_budget_s) if time_budget_s is not None else None

    # ── Two-axis chunking (checkpointing) ─────────────────────────
    # iteration_time_chunk_seconds = the per-invocation wall-clock cap; each
    #   such CHUNK resumes from the prior one (a measurement/checkpoint
    #   boundary, NOT a give-up). None ⇒ no chunking (one invocation per
    #   iteration, capped by agent.timeout_seconds as before).
    # iteration_max_time_seconds  = one ITERATION's total budget; keep
    #   chunking within an iteration until cumulative time hits this. None ⇒
    #   an iteration is a single chunk.
    chunk_s = iter_cfg.get("iteration_time_chunk_seconds", None)
    chunk_s = int(chunk_s) if chunk_s is not None else None
    iter_max_time_s = iter_cfg.get("iteration_max_time_seconds", None)
    iter_max_time_s = float(iter_max_time_s) if iter_max_time_s is not None else None
    chunking = chunk_s is not None
    if chunking:
        # Chunking implies resume (chunks continue from each other).
        resume_enabled = True

    # ── Sampled eval (preferred perf-vs-time mechanism) ──────────────
    # One uninterrupted agent run + a passive background sampler that snapshots
    # the editable source every ``eval.sample_interval`` seconds; each snapshot
    # is graded post-hoc (after the agent ends) into a perf-vs-time row. No
    # kills, no resume tax. Supersedes chunking. Enabled by ``eval.sampled=true``.
    if bool(cfg.eval.get("sampled", False)):
        return _sampled_run(
            cfg, run_root, sample_interval_s=float(cfg.eval.get("sample_interval", 120))
        )

    if mode_label not in {"eval", "self"}:
        raise SystemExit(f"iterate.mode must be 'eval' or 'self', got {mode_label!r}")

    logger.info(
        "iterate: mode={} max_retries={} stop_on_done={} budget_usd={} "
        "feedback={} resume={} time_budget_s={}",
        mode_label,
        max_retries,
        stop_on_done,
        budget_usd,
        feedback_enabled,
        resume_enabled,
        time_budget_s,
    )

    total_iterations = max_retries + 1
    records: list[IterationRecord] = []  # flat list of CHUNK records (perf points)
    cumulative_cost: float | None = None
    cumulative_seconds: float = 0.0
    stop_reason = "max_iterations"
    chunk_minutes = (chunk_s / 60.0) if chunk_s else None

    # ONE persistent working sandbox for the whole run. Every chunk edits it in
    # place; the codex session lives in its per-sandbox CODEX_HOME. Chunks after
    # the first RESUME that session (--last) so the agent's reasoning carries,
    # not just the on-disk files. Nothing is rebuilt between chunks OR between
    # iterations — an iteration boundary only injects a nudge. Per-chunk
    # metadata (artifact/eval/tokens) is still recorded under each chunk dir.
    work_source = run_root / "work" / "source" if chunking else None
    launched_any = False  # has any chunk run yet this run?

    def _run_chunk(
        chunk_dir: Path,
        *,
        it: int,
        ck: int,
        prev_feedback: str | None,
        cap_s: int | None,
    ) -> IterationRecord:
        nonlocal cumulative_cost, cumulative_seconds, launched_any
        # In-place chunking: resume the prior session after the first chunk.
        resume_session = chunking and launched_any
        rec = _run_one_iteration(
            cfg,
            chunk_dir,
            iteration_index=it,
            iteration_total=total_iterations,
            previous_feedback=prev_feedback,
            run_eval=(mode_label == "eval"),
            # Only the NON-chunking path seeds from a prior artifact; chunked
            # runs share the working dir on disk, so no overlay is needed.
            seed_artifact_path=None,
            timeout_override=cap_s,
            chunk_minutes=(cap_s / 60.0) if cap_s else chunk_minutes,
            work_source_dir=str(work_source) if work_source else None,
            resume_session=resume_session,
        )
        launched_any = True
        rec.iteration = it
        rec.chunk = ck
        rec.resumed_from = str(work_source) if resume_session else None
        records.append(rec)
        if rec.cost_usd is not None:
            cumulative_cost = (cumulative_cost or 0.0) + rec.cost_usd
        if rec.elapsed_seconds is not None:
            cumulative_seconds += rec.elapsed_seconds
        rec.cumulative_seconds = round(cumulative_seconds, 3)
        rec.cumulative_cost_usd = cumulative_cost
        if rec.build_seed_ok is False:
            logger.warning(
                "chunk it{}.ck{} artifact does not build — the next chunk "
                "continues from this state in place (agent fixes it, aided by "
                "session resume + eval feedback)",
                it,
                ck,
            )
        return rec

    def _iteration_nudge(it: int) -> str | None:
        """Feedback for the START of iteration ``it`` (it>0). Anti-laziness
        lives here: a new iteration means the previous one ended (gave up or
        exhausted its time budget); nudge the agent to keep going."""
        if not feedback_enabled:
            return (
                _blind_mode_nudge(it - 1, total_iterations)
                if mode_label == "eval"
                else None
            )
        if mode_label == "eval" and records:
            return _load_feedback_for_next(records[-1])
        return _self_mode_nudge(it - 1, total_iterations)

    # Bounded retries for TRANSIENT chunk failures (engine 404 / disconnect /
    # throttle): the agent process exits non-zero WITHOUT hitting the wall clock
    # and WITHOUT declaring done. Those must be retried (same chunk, same
    # resumed state) rather than mistaken for a give-up — otherwise a bedrock
    # blip silently truncates the eval. Give-up is ONLY a clean exit (ok=True).
    max_transient_retries = int(iter_cfg.get("max_transient_retries", 8))
    transient_backoff_s = float(iter_cfg.get("transient_backoff_seconds", 20))

    def _is_transient(rec: IterationRecord) -> bool:
        # non-timeout + agent NOT ok = process died on an error, not a give-up.
        return (rec.killed_by_timeout is not True) and (rec.agent_ok is False)

    stop = False
    for it in range(total_iterations):
        if stop:
            break
        logger.info("=== iteration {}/{} ===", it, total_iterations - 1)
        prev_feedback = None if it == 0 else _iteration_nudge(it)
        iter_elapsed = 0.0
        ck = 0
        transient_tries = 0
        while True:
            chunk_dir = run_root / (
                f"iter-{it}-chunk-{ck}" if chunking else f"iter-{it}"
            )
            rec = _run_chunk(
                chunk_dir, it=it, ck=ck, prev_feedback=prev_feedback, cap_s=chunk_s
            )

            # ── TRANSIENT failure (404/disconnect/engine overload): retry the
            # SAME chunk. Do not advance ck, do not count toward the iteration
            # budget, do not treat as give-up. Resume state is intact on disk.
            if chunking and _is_transient(rec):
                transient_tries += 1
                rec.ended_by = "transient_error"
                if transient_tries <= max_transient_retries:
                    logger.warning(
                        "iterate: it{}.ck{} TRANSIENT failure (agent_ok=False, "
                        "not timeout) — retry {}/{} after {:.0f}s",
                        it,
                        ck,
                        transient_tries,
                        max_transient_retries,
                        transient_backoff_s,
                    )
                    time.sleep(transient_backoff_s)
                    continue  # re-run same chunk index
                # Exhausted retries = the engine is sustainably unhealthy (e.g. a
                # concurrency-driven 404 storm). Do NOT write a terminal marker:
                # raise so the run ends WITHOUT TERMINAL, and the supervisor
                # relaunches this eval later (from its in-place resume state)
                # once load has dropped. A storm must never be recorded as a
                # real 'max_iterations' result.
                raise _TransientStorm(
                    f"it{it}.ck{ck}: {max_transient_retries} transient retries "
                    f"exhausted — engine unhealthy, deferring for relaunch"
                )
            transient_tries = 0

            # after the first successful chunk of an iteration, no more
            # re-entry nudge — chunks are silent measurement boundaries.
            prev_feedback = None
            iter_elapsed += rec.elapsed_seconds or 0.0

            # ── global stops (checked every chunk) ──
            if stop_on_done and rec.done:
                stop_reason, rec.ended_by, stop = "done", "all_pass", True
                logger.info("iterate: all specs pass at it{}.ck{}, stopping", it, ck)
                break
            if (
                budget_usd is not None
                and cumulative_cost is not None
                and cumulative_cost >= budget_usd
            ):
                stop_reason, stop = "budget_exceeded", True
                logger.info("iterate: cost {:.4f} ≥ cap, stopping", cumulative_cost)
                break
            if time_budget_s is not None and cumulative_seconds >= time_budget_s:
                stop_reason, stop = "time_budget_exceeded", True
                logger.info(
                    "iterate: cum wall-clock {:.0f}s ≥ cap {:.0f}s, stopping",
                    cumulative_seconds,
                    time_budget_s,
                )
                break

            # ── chunk-vs-iteration boundary ──
            if not chunking:
                rec.ended_by = "timeout" if rec.killed_by_timeout else "gave_up"
                break  # one chunk == one iteration; go to next iteration
            if rec.killed_by_timeout is not True and rec.agent_ok is True:
                # Agent EXITED CLEANLY before the chunk cutoff → gave up / thinks
                # it's done. End this iteration; anti-laziness = NEXT iteration.
                rec.ended_by = "gave_up"
                logger.info(
                    "iterate: agent exited early+clean at it{}.ck{} (gave up) — "
                    "ending iteration",
                    it,
                    ck,
                )
                break
            # Hit the chunk cutoff (still working) → checkpoint boundary. Resume
            # the next chunk silently, unless the iteration's time budget is up.
            rec.ended_by = "timeout"
            if iter_max_time_s is not None and iter_elapsed >= iter_max_time_s:
                logger.info(
                    "iterate: iteration {} hit its {:.0f}s budget after {} "
                    "chunk(s) — ending iteration",
                    it,
                    iter_max_time_s,
                    ck + 1,
                )
                break
            ck += 1

    best_index = _pick_best_index(records)

    summary = IterationSummary(
        mode=mode_label,
        max=max_retries,
        stop_reason=stop_reason,
        best_index=best_index,
        iterations=records,
        cumulative_cost_usd=cumulative_cost,
    )
    (run_root / "iterations.json").write_text(summary.to_json(), encoding="utf-8")

    # Durable terminal marker for a cross-process supervisor: a run that reached
    # a genuine terminal state (done / gave_up / time/budget cap / max_iterations)
    # writes DONE here. A relaunching supervisor treats presence of this file as
    # "this eval is complete — skip it"; its absence means the process died
    # mid-eval and should be relaunched (the in-place work dir resumes).
    (run_root / "TERMINAL").write_text(
        json.dumps(
            {
                "stop_reason": stop_reason,
                "best_passed": (
                    records[best_index].passed_specs if best_index is not None else None
                ),
                "best_total": (
                    records[best_index].total_specs if best_index is not None else None
                ),
                "chunks": len(records),
            }
        ),
        encoding="utf-8",
    )

    # Performance-vs-time table — one row per trial with cumulative wall-clock,
    # passed-specs, and token/cost spend. This is the headline artifact of a
    # resume run: it shows how solved-count climbs as compute-time accrues.
    _write_perf_vs_time(run_root, records, resume_enabled=resume_enabled)

    if best_index is not None:
        _mirror_best_for_backcompat(cfg, run_root, records[best_index])
        _write_top_level_manifest(cfg, run_root, records[best_index])

    logger.info(
        "iterate: stop_reason={} best_iter={} passed={} cumulative_cost={}",
        stop_reason,
        best_index,
        (records[best_index].passed_specs if best_index is not None else None),
        cumulative_cost,
    )
    return summary


# ─── Sampled run (perf-vs-time via a passive sampler) ───────────────


def _sampled_run(
    cfg: DictConfig, run_root: Path, *, sample_interval_s: float
) -> IterationSummary:
    """One uninterrupted agent run + post-hoc grading of periodic snapshots.

    The agent runs ONCE (capped only by ``agent.timeout_seconds``) while a
    background sampler copies its editable source every ``sample_interval_s``
    and reads live cumulative token usage. After the agent ends, every snapshot
    is graded with a full authoritative render, producing one perf-vs-time row
    each. Far simpler than chunking (no kill/resume) and denser (a point per
    sample, not per chunk). Transient-404 handling + TERMINAL marker are kept.
    """
    from vero.cli_dispatch import grade_snapshot
    from vero.generation.pricing import UnknownModelError, cost_from_usage

    # Sampled eval always grades (perf points come from grading). The iterate
    # group's mode is advisory here; default to "eval" when the group doesn't
    # set it (e.g. eval.sampled=true with iterate=off).
    iter_cfg = cfg.get("iterate", {}) if "iterate" in cfg else {}
    mode_label = str(iter_cfg.get("mode", "eval")) if iter_cfg else "eval"
    if mode_label not in {"eval"}:
        raise SystemExit("sampled run grades every snapshot — requires mode=eval")
    max_transient_retries = (
        int(iter_cfg.get("max_transient_retries", 8)) if iter_cfg else 8
    )
    transient_backoff_s = (
        float(iter_cfg.get("transient_backoff_seconds", 20)) if iter_cfg else 20.0
    )

    # Resolve the pricing model id the same way the codex agent does, so
    # sampled cost matches the agent's own cost accounting.
    model_id = None
    for ov in list(cfg.agent.get("config_overrides", []) or []):
        if isinstance(ov, str) and ov.startswith("model="):
            model_id = ov.split("=", 1)[1]
            break
    model_id = model_id or cfg.agent.get("model", None)

    # Run the agent (with sampler) — retry transient engine failures in place.
    gen = None
    tries = 0
    while True:
        gen = dispatch_generation(
            cfg,
            run_root,
            iteration_index=0,
            iteration_total=1,
            sample_interval_s=sample_interval_s,
        )
        transient = (gen.killed_by_timeout is not True) and (gen.agent_ok is False)
        if transient and tries < max_transient_retries:
            tries += 1
            logger.warning(
                "sampled: TRANSIENT agent failure — retry {}/{} after {:.0f}s",
                tries,
                max_transient_retries,
                transient_backoff_s,
            )
            time.sleep(transient_backoff_s)
            continue
        if transient:
            raise _TransientStorm(
                f"{max_transient_retries} transient retries exhausted — "
                f"engine unhealthy, deferring for relaunch"
            )
        break

    samples = gen.samples or []
    logger.info("sampled: grading {} snapshot(s) post-hoc", len(samples))

    records: list[IterationRecord] = []
    grade_root = run_root / "sample_grades"
    for i, samp in enumerate(samples):
        snap = Path(samp["snapshot"])
        grade_dir = grade_root / f"s{i:03d}"
        gr = grade_snapshot(cfg, snap, grade_dir)
        usage = samp.get("usage")
        # Cost: prefer the agent's own SDK cumulative cost when the sampler
        # captured it (claude — token-derived cost is unreliable there); else
        # compute from the sampled cumulative usage (codex).
        cost = samp.get("cost_usd")
        if cost is None:
            try:
                cost = (
                    cost_from_usage(model_id, usage) if (usage and model_id) else None
                )
            except UnknownModelError:
                cost = None
        rec = IterationRecord(
            index=0,
            source_dir=str(snap),
            artifact_path=str(snap / "artifact.json"),
            agent_ok=gen.agent_ok,
            num_turns=gen.num_turns,
            cost_usd=cost,
            usage=usage,
            elapsed_seconds=samp.get("elapsed_s"),
            killed_by_timeout=gen.killed_by_timeout,
            iteration=0,
            chunk=i,
        )
        rec.cumulative_seconds = samp.get("elapsed_s")
        rec.cumulative_cost_usd = cost
        if gr.get("gradable"):
            rec.eval_dir = str(grade_dir)
            rec.build_ok = gr["build_ok"]
            rec.passed_specs = gr["passed_specs"]
            rec.total_specs = gr["total_specs"]
            rec.unfilled_specs = gr["unfilled_specs"]
            rec.failed_specs = gr["failed_specs"]
            rec.joint_passed = gr["joint_passed"]
            rec.done = (
                gr["build_ok"]
                and gr["passed_specs"] == gr["total_specs"]
                and gr["unfilled_specs"] == 0
            )
        rec.ended_by = (
            "all_pass"
            if rec.done
            else ("sample" if i < len(samples) - 1 else "gave_up")
        )
        records.append(rec)

    best_index = _pick_best_index(records)
    stop_reason = (
        "done" if (best_index is not None and records[best_index].done) else "gave_up"
    )

    summary = IterationSummary(
        mode=mode_label,
        max=0,
        stop_reason=stop_reason,
        best_index=best_index,
        iterations=records,
        cumulative_cost_usd=records[-1].cumulative_cost_usd if records else None,
    )
    (run_root / "iterations.json").write_text(summary.to_json(), encoding="utf-8")
    (run_root / "TERMINAL").write_text(
        json.dumps(
            {
                "stop_reason": stop_reason,
                "best_passed": (
                    records[best_index].passed_specs if best_index is not None else None
                ),
                "best_total": (
                    records[best_index].total_specs if best_index is not None else None
                ),
                "chunks": len(records),
            }
        ),
        encoding="utf-8",
    )
    _write_perf_vs_time(run_root, records, resume_enabled=False)
    if best_index is not None:
        _mirror_best_for_backcompat(cfg, run_root, records[best_index])
        _write_top_level_manifest(cfg, run_root, records[best_index])
    logger.info(
        "sampled: stop_reason={} best_iter={} passed={} points={} cost={}",
        stop_reason,
        best_index,
        (records[best_index].passed_specs if best_index is not None else None),
        len(records),
        summary.cumulative_cost_usd,
    )
    return summary


# ─── Per-iteration step ─────────────────────────────────────────────


def _run_one_iteration(
    cfg: DictConfig,
    iter_root: Path,
    *,
    iteration_index: int,
    iteration_total: int,
    previous_feedback: str | None,
    run_eval: bool,
    seed_artifact_path: str | None = None,
    timeout_override: int | None = None,
    chunk_minutes: float | None = None,
    work_source_dir: str | None = None,
    resume_session: bool = False,
) -> IterationRecord:
    """Run generation and (optionally) eval for a single CHUNK.
    Returns a fully-populated :class:`IterationRecord`.

    ``seed_artifact_path`` (non-chunked resume) seeds this chunk's sandbox from
    a prior artifact. ``work_source_dir`` (chunked runs) points the agent at a
    shared persistent working sandbox edited in place; ``resume_session``
    continues the prior codex session there. ``timeout_override`` caps this
    chunk; ``chunk_minutes`` drives the INSTRUCTION wind-down pacing.
    """
    iter_root.mkdir(parents=True, exist_ok=True)

    gen = dispatch_generation(
        cfg,
        iter_root,
        previous_feedback=previous_feedback,
        iteration_index=iteration_index,
        iteration_total=iteration_total,
        seed_artifact_path=seed_artifact_path,
        timeout_override=timeout_override,
        chunk_minutes=chunk_minutes,
        work_source_dir=work_source_dir,
        resume_session=resume_session,
    )
    record = IterationRecord(
        index=iteration_index,
        source_dir=str(iter_root / "source"),
        artifact_path=str(gen.artifact_path),
        agent_ok=gen.agent_ok,
        num_turns=gen.num_turns,
        cost_usd=gen.total_cost_usd,
        usage=gen.usage,
        elapsed_seconds=gen.elapsed_seconds,
        killed_by_timeout=gen.killed_by_timeout,
    )

    if run_eval:
        eval_result = dispatch_evaluation(cfg, iter_root)
        if eval_result is not None:
            s = eval_result.report.summary
            record.eval_dir = str(iter_root / "eval" / cfg.eval.name)
            record.build_ok = bool(eval_result.report.build_ok)
            record.passed_specs = int(s.passed_specs)
            record.total_specs = int(s.total_specs)
            record.unfilled_specs = int(s.unfilled_specs)
            record.failed_specs = int(s.failed_specs)
            record.joint_passed = bool(s.joint_passed)
            # Done = build ok + every spec passed (per-grader). The grader
            # already enforces that a `sat_<S>` only counts toward
            # `passed_specs` when paired with a verified joint claim
            # (otherwise it grades `unpaired_sat`), and `prove_<S>` /
            # `unsat_<S>` pass on their own. So `passed_specs ==
            # total_specs` ⇔ every spec resolved via *some* valid path
            # (prove, unsat, or sat+joint). `joint_passed` is recorded
            # for diagnostics but is NOT a separate stop criterion: if
            # the agent solves everything via prove or unsat, no joint
            # is needed, and demanding `joint_passed=True` would force
            # wasted iterations.
            record.done = (
                record.build_ok
                and record.passed_specs == record.total_specs
                and record.unfilled_specs == 0
            )
            # The resume safety net keys off whether THIS chunk's artifact
            # builds: a chunk whose extracted state doesn't compile must NOT
            # poison the next chunk's seed.
            record.build_seed_ok = record.build_ok
    return record


# ─── Performance-vs-time reporting ─────────────────────────────────


def _tok(usage: dict[str, int] | None, key: str) -> int:
    return int(usage.get(key, 0)) if usage else 0


def _write_perf_vs_time(
    run_root: Path, records: list[IterationRecord], *, resume_enabled: bool
) -> None:
    """Write ``perf_vs_time.json`` + ``perf_vs_time.md`` — solved-vs-time.

    One row per trial: cumulative wall-clock (minutes), passed / total specs,
    tokens (input incl. cached, output incl. reasoning), and cumulative cost.
    The point of a resume run is to read this table top-to-bottom and see how
    many more specs each additional 30-min trial closes.
    """
    rows = []
    for i, r in enumerate(records):
        rows.append(
            {
                "checkpoint": i,  # position along the perf-vs-time curve
                "iteration": r.iteration,
                "chunk": r.chunk,
                "ended_by": r.ended_by,  # timeout | gave_up | all_pass
                "resumed": r.resumed_from is not None,
                "chunk_seconds": r.elapsed_seconds,
                "cumulative_seconds": r.cumulative_seconds,
                "cumulative_minutes": (
                    round(r.cumulative_seconds / 60.0, 1)
                    if r.cumulative_seconds is not None
                    else None
                ),
                "passed_specs": r.passed_specs,
                "total_specs": r.total_specs,
                "unfilled_specs": r.unfilled_specs,
                "failed_specs": r.failed_specs,
                "build_ok": r.build_ok,
                "done": r.done,
                "input_tokens": _tok(r.usage, "input_tokens"),
                "cached_input_tokens": _tok(r.usage, "cached_input_tokens"),
                "output_tokens": _tok(r.usage, "output_tokens"),
                "reasoning_output_tokens": _tok(r.usage, "reasoning_output_tokens"),
                "chunk_cost_usd": r.cost_usd,
                "cumulative_cost_usd": r.cumulative_cost_usd,
            }
        )
    (run_root / "perf_vs_time.json").write_text(
        json.dumps({"resume": resume_enabled, "rows": rows}, indent=2),
        encoding="utf-8",
    )

    # Human-readable companion.
    hdr = (
        "| it.ck | ended | cum.min | passed/total | unfilled | fail | build | "
        "in(tok) | out+reason(tok) | cum.$ |"
    )
    sep = "|---|---|---|---|---|---|---|---|---|---|"
    lines = ["# Performance vs. time", "", f"resume={resume_enabled}", "", hdr, sep]
    for r in rows:
        pt = (
            f"{r['passed_specs']}/{r['total_specs']}"
            if r["passed_specs"] is not None
            else "—"
        )
        cm = r["cumulative_minutes"] if r["cumulative_minutes"] is not None else "—"
        cost = (
            f"{r['cumulative_cost_usd']:.2f}"
            if r["cumulative_cost_usd"] is not None
            else "—"
        )
        out_reason = r["output_tokens"] + r["reasoning_output_tokens"]
        itck = (
            f"{r['iteration']}.{r['chunk']}"
            if r["iteration"] is not None
            else str(r["checkpoint"])
        )
        lines.append(
            f"| {itck} | {r['ended_by'] or '—'} | {cm} | {pt} | "
            f"{r['unfilled_specs']} | {r['failed_specs']} | {r['build_ok']} | "
            f"{r['input_tokens']} | {out_reason} | {cost} |"
        )
    (run_root / "perf_vs_time.md").write_text("\n".join(lines) + "\n", encoding="utf-8")
    logger.info("wrote perf-vs-time table ({} checkpoints) → {}", len(rows), run_root)


# ─── Feedback construction ─────────────────────────────────────────


def _load_feedback_for_next(record: IterationRecord) -> str | None:
    """Read the prior iteration's ``report.md`` into memory so the next
    iteration's sandbox can embed it into INSTRUCTION + drop it as
    ``FEEDBACK.md`` for the agent to re-open.
    """
    if not record.eval_dir:
        return None
    report_md = Path(record.eval_dir) / "report.md"
    if not report_md.is_file():
        logger.warning("feedback unavailable: {} missing", report_md)
        return None
    try:
        return report_md.read_text(encoding="utf-8")
    except OSError as err:
        logger.warning("failed to read {}: {}", report_md, err)
        return None


def _self_mode_nudge(iter_index: int, iter_total: int) -> str:
    """INSTRUCTION addendum for ``iterate.mode=self``: no grader report,
    just a reminder that the agent is re-entering and must re-assess."""
    next_index = iter_index + 1
    return (
        f"You are re-entering this sandbox on iteration {next_index} of "
        f"{iter_total - 1} retries. Re-assess whether every spec is "
        f"filled and the Done condition is met. If not, keep working — "
        f"fill every unfilled slot, fix failing proofs, and never bulk-"
        f"revert previously-compiling work."
    )


def _blind_mode_nudge(iter_index: int, iter_total: int) -> str:
    """INSTRUCTION addendum for blind iteration (``iterate.mode=eval``
    + ``iterate.feedback=false``): the prior attempt was graded but the
    report is hidden — tell the agent only that it isn't done yet so it
    doesn't quit early thinking the previous turn finished the job."""
    next_index = iter_index + 1
    return (
        f"You are re-entering this sandbox on iteration {next_index} of "
        f"{iter_total - 1} retries. The previous attempt did not satisfy "
        f"the build + spec criteria — keep working: fill every unfilled "
        f"marker, fix any failing proofs, and run `lake build` until it "
        f"succeeds with no `sorry` remaining."
    )


# ─── Best-iteration selection + back-compat mirroring ──────────────


def _pick_best_index(records: list[IterationRecord]) -> int | None:
    """Choose the best CHUNK by ``passed_specs`` desc, tie-broken by the
    EARLIEST checkpoint (least cumulative time for the same score — the
    natural pick on a perf-vs-time curve). Chunks without eval data
    (self-mode) score -1 so they only win if alone. Returns the LIST
    POSITION (records[i]), or ``None`` when ``records`` is empty.
    """
    if not records:
        return None
    best_i = 0
    for i, r in enumerate(records):
        lhs = r.passed_specs if r.passed_specs is not None else -1
        rhs = (
            records[best_i].passed_specs
            if records[best_i].passed_specs is not None
            else -1
        )
        # strictly-greater wins; ties keep the earlier (lower i) chunk.
        if lhs > rhs:
            best_i = i
    return best_i


def _mirror_best_for_backcompat(
    cfg: DictConfig, run_root: Path, best: IterationRecord
) -> None:
    """Copy the best iteration's ``source/`` and ``eval/<name>/`` up to
    the run root so the existing aggregator (which looks at
    ``<run>/eval/<name>/report.json``) keeps working without being
    taught about ``iter-N/`` layouts.
    """
    src = Path(best.source_dir)
    if src.is_dir():
        dst = run_root / "source"
        if dst.exists():
            shutil.rmtree(dst)
        shutil.copytree(src, dst)

    if best.eval_dir:
        eval_src = Path(best.eval_dir)
        if eval_src.is_dir():
            eval_dst = run_root / "eval" / cfg.eval.name
            if eval_dst.exists():
                shutil.rmtree(eval_dst)
            eval_dst.parent.mkdir(parents=True, exist_ok=True)
            shutil.copytree(eval_src, eval_dst)


def _write_top_level_manifest(
    cfg: DictConfig, run_root: Path, best: IterationRecord
) -> None:
    """Write ``<run>/manifest.json`` pointing at the mirrored best
    iteration's artifact. Mirrors ``cli._write_manifest`` for back-compat."""
    from vero.cli import _write_manifest  # local import avoids cycle

    artifact_path = run_root / "source" / "artifact.json"
    _write_manifest(
        cfg, run_root, artifact_path=artifact_path if artifact_path.exists() else None
    )


# ─── Helpers exported for tests ─────────────────────────────────────

__all__ = [
    "IterationRecord",
    "IterationSummary",
    "iterate_run",
]


# Typing import avoided at module top to keep imports tight.
_: Any = None
