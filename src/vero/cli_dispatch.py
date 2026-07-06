"""Adapter layer between ``vero.cli`` (hydra DictConfig) and the
existing runners in ``vero.generation.runner`` / ``vero.evaluation.runner``.

Keeping dispatch out of ``cli.py`` lets us unit-test it without needing
to stand up a full hydra config tree.
"""

from __future__ import annotations

import json
import shutil
import sys
from dataclasses import dataclass
from datetime import datetime
from pathlib import Path
from typing import Any

from loguru import logger
from omegaconf import DictConfig

from vero.generation.benchmark import Benchmark
from vero.generation.extractor import extract, read_artifact, write_artifact
from vero.generation.sandbox import create_sandbox


class _GenSampler:
    """Background daemon that snapshots a running agent's editable source +
    reads its live cumulative usage/cost on a fixed interval.

    Purpose: build a dense performance-vs-time curve WITHOUT killing/resuming
    the agent (the old chunking approach). We copy the editable ``.lean`` files
    aside so each snapshot can be graded post-hoc, and read whatever live
    telemetry the active agent streams to disk during the run:

    * **codex** — writes a ``token_count`` stream to its rollout JSONL
      (~1 event / 6-10 s); we recover cumulative ``total_token_usage``. Cost is
      computed downstream from that usage via :mod:`pricing`.
    * **claude** — writes an ``ev=result`` line per turn to the sandbox's
      ``agent_events.jsonl`` carrying ``cumulative_cost_usd`` + ``usage``; we
      take the SDK's cumulative cost directly (token-derived cost is unreliable
      for Claude — see ``ClaudeAgent._resolve_costs``).

    Both are cheap: a small file copy + one JSONL tail per tick, no Lean build
    on the hot path. Agent-agnostic on the snapshot side; the progress reader
    is dispatched on ``agent_kind`` and returns ``None`` for unknown agents (so
    the perf curve still gets snapshots/timestamps, just no usage/cost).
    """

    # Only these are worth snapshotting; everything else is frozen or cache.
    _EXCLUDE_DIRS = {".lake", "build", ".git", "__pycache__", ".codex_home"}

    def __init__(
        self,
        source_dir: Path,
        samples_root: Path,
        interval_s: float,
        *,
        agent_kind: str = "codex",
    ):
        import threading

        self._source = source_dir
        self._root = samples_root
        self._interval = max(5.0, float(interval_s))
        self._agent_kind = agent_kind
        self._codex_home = source_dir / ".codex_home"
        self._events_jsonl = source_dir / "agent_events.jsonl"
        self._t0 = None
        self._samples: list[dict] = []
        self._stop = threading.Event()
        self._thread = threading.Thread(target=self._loop, daemon=True)

    def _snapshot(self, tag: str) -> str:
        dst = self._root / tag
        dst.mkdir(parents=True, exist_ok=True)
        for f in self._source.rglob("*"):
            if not f.is_file():
                continue
            rel = f.relative_to(self._source)
            if any(part in self._EXCLUDE_DIRS for part in rel.parts):
                continue
            if f.suffix != ".lean" and f.name != "manifest.json":
                continue
            out = dst / rel
            out.parent.mkdir(parents=True, exist_ok=True)
            try:
                shutil.copy2(f, out)
            except OSError:
                pass
        return str(dst)

    def _read_progress(self) -> dict:
        """Return ``{"usage": dict|None, "cost_usd": float|None}`` from the
        active agent's live on-disk telemetry. Best-effort — never raises."""
        try:
            if self._agent_kind == "codex":
                from vero.generation.agents.codex import CodexAgent

                usage = CodexAgent._usage_from_rollout(str(self._codex_home))
                return {"usage": usage, "cost_usd": None}
            if self._agent_kind == "claude":
                return self._read_claude_events()
        except Exception:
            pass
        return {"usage": None, "cost_usd": None}

    def _read_claude_events(self) -> dict:
        """Read the LAST ``ev=result`` line of the sandbox's
        ``agent_events.jsonl`` — Claude writes one per turn (line-buffered)
        with cumulative SDK cost + usage. The SDK ``cumulative_cost_usd`` is
        authoritative for Claude (token-derived cost runs 3-9× off)."""
        if not self._events_jsonl.is_file():
            return {"usage": None, "cost_usd": None}
        usage = None
        cost = None
        try:
            with self._events_jsonl.open(encoding="utf-8", errors="replace") as fh:
                for line in fh:
                    if '"result"' not in line:
                        continue
                    try:
                        ev = json.loads(line)
                    except json.JSONDecodeError:
                        continue
                    if ev.get("ev") != "result":
                        continue
                    u = ev.get("usage")
                    if isinstance(u, dict):
                        usage = {
                            k: v for k, v in u.items() if isinstance(v, (int, float))
                        }
                    c = ev.get("cumulative_cost_usd")
                    if isinstance(c, (int, float)):
                        cost = float(c)
        except OSError:
            return {"usage": None, "cost_usd": None}
        return {"usage": usage, "cost_usd": cost}

    def _take(self, tag: str) -> None:
        import time

        elapsed = 0.0 if self._t0 is None else time.monotonic() - self._t0
        prog = self._read_progress()
        self._samples.append(
            {
                "elapsed_s": round(elapsed, 1),
                "usage": prog.get("usage"),
                "cost_usd": prog.get("cost_usd"),
                "snapshot": self._snapshot(tag),
            }
        )

    def _loop(self) -> None:
        i = 0
        while not self._stop.wait(self._interval):
            i += 1
            try:
                self._take(f"t{i:03d}_{int(self._samples_elapsed())}s")
            except Exception as e:  # never let the sampler crash the run
                logger.warning("gen sampler tick failed: {}", e)

    def _samples_elapsed(self) -> float:
        import time

        return 0.0 if self._t0 is None else time.monotonic() - self._t0

    def start(self) -> None:
        import time

        self._t0 = time.monotonic()
        self._thread.start()

    def finish(self) -> list[dict]:
        """Stop sampling and take the authoritative final snapshot."""
        self._stop.set()
        self._thread.join(timeout=self._interval + 5)
        try:
            self._take("final")
        except Exception as e:
            logger.warning("gen sampler final snapshot failed: {}", e)
        return self._samples


@dataclass
class GenerationDispatchResult:
    """Small envelope so callers (cli, iterate harness) can read
    agent-reported cost / turns without re-parsing ``agent_events.jsonl``.
    """

    artifact_path: Path
    agent_ok: bool | None = None
    num_turns: int | None = None
    total_cost_usd: float | None = None
    # Token usage dict from the agent (input/output/cached/reasoning tokens)
    # and wall-clock seconds — surfaced so the trial loop can chart
    # performance-vs-time and per-trial token spend.
    usage: dict[str, int] | None = None
    elapsed_seconds: float | None = None
    # True ⇒ the chunk hit its wall-clock cap (agent still working → resume the
    # next chunk); False ⇒ the agent exited on its own (declared done / gave up
    # → end the iteration). None ⇒ unknown (skip_agent or non-codex).
    killed_by_timeout: bool | None = None
    # Passive mid-run samples for the perf-vs-time curve (populated only when a
    # sampler ran). Each: {elapsed_s: float, usage: dict|None, snapshot: str}
    # where ``snapshot`` is a dir holding the editable source at that instant,
    # graded post-hoc. The final entry is the true end-of-run state.
    samples: list[dict] | None = None


def _resolve_benchmark_dir(cfg: DictConfig) -> Path:
    from vero.cli import _resolve_under_repo  # local import: avoids cycle

    return _resolve_under_repo(cfg.benchmark.path)


# ─── Generation ────────────────────────────────────────────────────


def dispatch_generation(
    cfg: DictConfig,
    run_root: Path,
    *,
    previous_feedback: str | None = None,
    iteration_index: int = 0,
    iteration_total: int = 1,
    seed_artifact_path: Path | str | None = None,
    timeout_override: int | None = None,
    chunk_minutes: float | None = None,
    resume_session: bool = False,
    work_source_dir: Path | str | None = None,
    sample_interval_s: float | None = None,
) -> GenerationDispatchResult:
    """Materialize source sandbox, optionally run the agent, extract artifact.

    Returns a :class:`GenerationDispatchResult` carrying the artifact
    path plus (when the agent ran) its ok/turns/cost/usage/elapsed numbers.

    ``previous_feedback``, ``iteration_index``, ``iteration_total`` are
    threaded into the rendered INSTRUCTION template and — if feedback is
    provided — written to ``source/FEEDBACK.md``. Defaults preserve the
    single-shot behaviour (no feedback, iteration 0 of 1).

    ``seed_artifact_path`` (RESUME) — when set, the fresh sandbox is
    pre-filled from that prior ``artifact.json`` so the agent continues
    from previous progress instead of blank stubs.

    ``timeout_override`` — per-chunk wall-clock cap (seconds); overrides
    ``cfg.agent.timeout_seconds`` for this invocation. Used by the chunked
    iterate loop to cap each checkpoint at ``iteration_time_chunk``.
    ``chunk_minutes`` — surfaced into the INSTRUCTION so the agent can pace
    its wind-down for the checkpoint (see render_instruction).
    """
    # The agent's WORKING sandbox. Normally ``run_root/source``. For chunked
    # runs the loop passes a single persistent ``work_source_dir`` shared by
    # every chunk (edits + codex session live there and are never rebuilt);
    # per-chunk metadata (artifact/eval) still lands under ``run_root/source``.
    metadata_source_dir = run_root / "source"
    source_dir = (
        Path(work_source_dir) if work_source_dir is not None else metadata_source_dir
    )
    in_place = source_dir.is_dir() and (source_dir / "INSTRUCTION.md").is_file()
    benchmark_dir = _resolve_benchmark_dir(cfg)
    if timeout_override is not None:
        # Deep-copy so the override is scoped to this chunk, and disable struct
        # mode so writing the (existing) key can't trip on a frozen schema.
        from omegaconf import OmegaConf

        cfg = OmegaConf.create(OmegaConf.to_container(cfg, resolve=False))
        OmegaConf.set_struct(cfg, False)
        cfg.agent.timeout_seconds = int(timeout_override)

    seed_artifact = None
    if seed_artifact_path is not None:
        seed_path = Path(seed_artifact_path)
        if seed_path.is_file():
            seed_artifact = read_artifact(seed_path)
            logger.info("resume: seeding sandbox from prior artifact {}", seed_path)
        else:
            logger.warning(
                "resume: seed_artifact_path {} not found — starting from blank stubs",
                seed_path,
            )

    bench = Benchmark(benchmark_dir)

    if in_place and source_dir.is_dir():
        # IN-PLACE chunk: reuse the existing working sandbox (files + codex
        # session already on disk). Do NOT re-render — that would wipe the
        # agent's edits and its session. Only refresh the INSTRUCTION so this
        # chunk gets its wind-down pacing / iteration nudge, then re-run.
        logger.info("in-place chunk: reusing working sandbox at {}", source_dir)
        from vero.generation.prompt import render_instruction

        (source_dir / "INSTRUCTION.md").write_text(
            render_instruction(
                bench,
                mode=cfg.mode,
                previous_feedback=previous_feedback,
                iteration_index=iteration_index,
                iteration_total=iteration_total,
                chunk_minutes=chunk_minutes,
            ),
            encoding="utf-8",
        )
        if previous_feedback is not None:
            (source_dir / "FEEDBACK.md").write_text(previous_feedback, encoding="utf-8")
    else:
        logger.info("materializing sandbox at {}", source_dir)
        # source_context (lean|full) is an eval-config knob: full ships the
        # prefetched upstream source into the sandbox as agent reference.
        source_context = str(cfg.eval.get("source_context", "lean"))
        create_sandbox(
            benchmark_dir,
            source_dir,
            mode=cfg.mode,
            overwrite=True,  # run_root is already checked by cli.main
            previous_feedback=previous_feedback,
            iteration_index=iteration_index,
            iteration_total=iteration_total,
            seed_artifact=seed_artifact,
            chunk_minutes=chunk_minutes,
            source_context=source_context,
        )

    agent_ok: bool | None = None
    num_turns: int | None = None
    total_cost_usd: float | None = None
    usage: dict[str, int] | None = None
    elapsed_seconds: float | None = None
    killed_by_timeout: bool | None = None
    samples: list[dict] | None = None
    if cfg.skip_agent:
        logger.info(
            "skip_agent=true → sandbox materialized but agent not invoked. "
            "Extracting no-op artifact for shape consistency."
        )
    else:
        agent = _build_agent(cfg)
        _attach_env_shim(agent, cfg, source_dir)
        # Session continuity: chunks after the first (within an in-place working
        # sandbox) resume the prior codex session — the agent's reasoning
        # carries, not just the on-disk files. Same dir ⇒ same per-sandbox
        # CODEX_HOME + same cwd ⇒ `codex exec resume --last` finds it.
        if resume_session and hasattr(agent, "resume_session"):
            agent.resume_session = True
        logger.info(
            "running agent={} model={} in {}",
            agent.name,
            getattr(agent, "model", "?"),
            source_dir,
        )
        instruction_file = source_dir / "INSTRUCTION.md"
        sampler = None
        if sample_interval_s is not None:
            sampler = _GenSampler(
                source_dir,
                run_root / "samples",
                float(sample_interval_s),
                agent_kind=agent.name,
            )
            sampler.start()
            logger.info(
                "gen sampler on ({}): every {:.0f}s → {}",
                agent.name,
                sample_interval_s,
                run_root / "samples",
            )
        try:
            result = agent.run(
                sandbox_dir=source_dir, instruction_file=instruction_file
            )
        finally:
            if sampler is not None:
                samples = sampler.finish()
                logger.info("gen sampler collected {} snapshot(s)", len(samples or []))
        logger.info(
            "agent finished: ok={} turns={} cost={}",
            result.ok,
            result.num_turns,
            result.total_cost_usd,
        )
        agent_ok = bool(result.ok)
        num_turns = int(result.num_turns)
        total_cost_usd = result.total_cost_usd
        usage = dict(result.usage) if result.usage else None
        elapsed_seconds = result.elapsed_seconds
        kbt = (result.extra or {}).get("killed_by_timeout")
        killed_by_timeout = bool(kbt) if kbt is not None else None

    # Extract from the WORKING dir (where the agent edited), and record the
    # artifact as this chunk's metadata under run_root/source so per-chunk eval
    # + the perf-vs-time point are preserved even though chunks share one
    # working sandbox.
    artifact = extract(source_dir, bench, mode=cfg.mode)
    write_artifact(artifact, source_dir / "artifact.json")
    if metadata_source_dir != source_dir:
        metadata_source_dir.mkdir(parents=True, exist_ok=True)
        write_artifact(artifact, metadata_source_dir / "artifact.json")
        # The agent's event log / transcript lives in the SHARED working dir and
        # is truncated by the next chunk's run. Snapshot this chunk's transcript
        # into its own metadata dir so per-chunk history is preserved.
        for fname in ("agent_events.jsonl", "agent.log"):
            src_f = source_dir / fname
            if src_f.is_file():
                (metadata_source_dir / fname).write_text(
                    src_f.read_text(encoding="utf-8", errors="replace"),
                    encoding="utf-8",
                )
    artifact_path = metadata_source_dir / "artifact.json"
    logger.info("wrote artifact: {} slots → {}", len(artifact.slots), artifact_path)
    return GenerationDispatchResult(
        artifact_path=artifact_path,
        agent_ok=agent_ok,
        num_turns=num_turns,
        total_cost_usd=total_cost_usd,
        usage=usage,
        elapsed_seconds=elapsed_seconds,
        killed_by_timeout=killed_by_timeout,
        samples=samples,
    )


def _build_agent(cfg: DictConfig):
    from vero.generation.agents.base import create_agent

    agent_cfg = dict(cfg.agent)
    kind = agent_cfg.pop("kind")
    # `env:` / `dotfiles:` / `config_files:` are consumed by the shim (see
    # `_attach_env_shim`) not by the agent constructors. Strip them before
    # splatting into kwargs.
    agent_cfg.pop("env", None)
    agent_cfg.pop("dotfiles", None)
    agent_cfg.pop("config_files", None)
    return create_agent(kind, **{k: v for k, v in agent_cfg.items() if v is not None})


def _attach_env_shim(agent, cfg: DictConfig, source_dir: Path) -> None:
    """Build an `AgentEnvShim` from the Hydra agent config and attach it.

    Currently applies to `claude` + `codex` only. Gemini/gauss keep their
    in-agent env plumbing until validated on the first two.
    """
    from vero.generation.agents.env_shim import shim_from_config

    kind = agent.name
    if kind not in {"claude", "codex"}:
        return
    shim = shim_from_config(kind, source_dir, dict(cfg.agent))
    setattr(agent, "env_shim", shim)


# ─── Evaluation ────────────────────────────────────────────────────


def dispatch_evaluation(cfg: DictConfig, run_root: Path) -> Any:
    """Re-render a fresh eval sandbox under ``<run_root>/eval/<cfg.eval.name>/``
    and grade it. Returns the :class:`EvaluationRunResult` so callers
    (iterate harness) can inspect pass/fail counts and paths.
    """
    from vero.evaluation.runner import run_evaluation
    from vero.generation.extractor import Artifact, ExtractedSlot, ExtraSlot

    eval_dir = run_root / "eval" / cfg.eval.name
    if eval_dir.exists():
        if not cfg.eval.overwrite:
            raise SystemExit(
                f"eval dir {eval_dir} already exists; pass eval.overwrite=true "
                f"to replace (or pick a different eval.name=)."
            )
        shutil.rmtree(eval_dir)
    eval_dir.mkdir(parents=True, exist_ok=True)
    eval_sandbox = eval_dir / "sandbox"

    artifact_path = run_root / "source" / "artifact.json"
    if not artifact_path.is_file():
        raise SystemExit(
            f"no artifact at {artifact_path}; was generation skipped for this run?"
        )
    data = json.loads(artifact_path.read_text(encoding="utf-8"))
    artifact = Artifact(
        benchmark_id=data["benchmark_id"],
        mode=data["mode"],
        sandbox_dir=data.get("sandbox_dir", ""),
        slots=[ExtractedSlot(**s) for s in data.get("slots", [])],
        extras=[ExtraSlot(**x) for x in data.get("extras", [])],
        file_errors=dict(data.get("file_errors", {})),
    )
    if artifact.mode != cfg.mode:
        raise SystemExit(
            f"artifact mode {artifact.mode!r} does not match run mode {cfg.mode!r}"
        )

    benchmark_dir = _resolve_benchmark_dir(cfg)
    log_sink_id = _open_eval_log(eval_dir / "eval.log")

    started_at = datetime.now()
    try:
        result = run_evaluation(
            benchmark_dir=benchmark_dir,
            artifact=artifact,
            mode=cfg.mode,
            eval_sandbox_dir=eval_sandbox,
            report_dir=eval_dir,
            lake_timeout=cfg.eval.timeout,
        )
    finally:
        logger.remove(log_sink_id)

    elapsed = (datetime.now() - started_at).total_seconds()
    _write_eval_manifest(cfg, run_root, eval_dir, started_at, elapsed, result)

    s = result.report.summary
    logger.info(
        "eval done: build_ok={} passed={}/{} failed={} unfilled={} joint={} → {}",
        result.report.build_ok,
        s.passed_specs,
        s.total_specs,
        s.failed_specs,
        s.unfilled_specs,
        s.joint_passed,
        result.md_path,
    )

    # Opt-in anti-cheat judge over `instance` declarations.
    if cfg.eval.get("check_instances", False):
        from vero.evaluation.instance_check import run_instance_check

        logger.info("eval.check_instances=true — dispatching LLM instance judge")
        run_instance_check(
            run_root,
            {
                "model": cfg.eval.get("check_instances_model", "gpt-5.5"),
                "max_concurrency": int(cfg.eval.get("check_instances_concurrency", 8)),
                "eval_name": cfg.eval.name,
            },
        )

    return result


def grade_snapshot(
    cfg: DictConfig, snapshot_dir: Path, report_dir: Path
) -> dict[str, Any]:
    """Grade one mid-run source SNAPSHOT with a full authoritative render.

    Used by the sampled-eval path: extract the artifact from ``snapshot_dir``
    (the editable ``.lean`` state at some instant), then re-render a fresh
    anti-cheat eval sandbox under ``report_dir`` and grade it — identical
    machinery to :func:`dispatch_evaluation`, just sourced from a snapshot
    rather than the live working dir. Returns pass/total/build_ok (or
    ``{"gradable": False}`` if the snapshot has no extractable artifact).
    """
    bench = Benchmark(_resolve_benchmark_dir(cfg))
    try:
        artifact = extract(snapshot_dir, bench, mode=cfg.mode)
    except Exception as e:
        logger.warning("snapshot {} not extractable: {}", snapshot_dir, e)
        return {"gradable": False}

    from vero.evaluation.runner import run_evaluation

    report_dir.mkdir(parents=True, exist_ok=True)
    sandbox = report_dir / "sandbox"
    try:
        result = run_evaluation(
            benchmark_dir=_resolve_benchmark_dir(cfg),
            artifact=artifact,
            mode=cfg.mode,
            eval_sandbox_dir=sandbox,
            report_dir=report_dir,
            lake_timeout=cfg.eval.timeout,
        )
    except Exception as e:
        logger.warning("snapshot grade failed for {}: {}", snapshot_dir, e)
        return {"gradable": False}
    s = result.report.summary
    return {
        "gradable": True,
        "build_ok": bool(result.report.build_ok),
        "passed_specs": int(s.passed_specs),
        "total_specs": int(s.total_specs),
        "unfilled_specs": int(s.unfilled_specs),
        "failed_specs": int(s.failed_specs),
        "joint_passed": bool(s.joint_passed),
    }


def _open_eval_log(path: Path) -> int:
    """Mirror loguru into ``eval.log`` for the duration of the eval."""
    return logger.add(
        path,
        format="{time:YYYY-MM-DD HH:mm:ss.SSS} | {level: <8} | {name}:{function}:{line} - {message}",
        level="DEBUG",
        backtrace=False,
        diagnose=False,
    )


def _write_eval_manifest(
    cfg: DictConfig,
    run_root: Path,
    eval_dir: Path,
    started_at: datetime,
    elapsed_seconds: float,
    result: Any,
) -> None:
    from vero.cli import _git_sha

    manifest = {
        "eval_name": cfg.eval.name,
        "against_run": cfg.name,
        "mode": cfg.mode,
        "started_at": started_at.isoformat(timespec="seconds"),
        "elapsed_seconds": round(elapsed_seconds, 3),
        "git_sha": _git_sha(),
        "python": sys.version.split()[0],
        "lake_timeout": cfg.eval.timeout,
        "summary": {
            "build_ok": bool(result.report.build_ok),
            "total_specs": result.report.summary.total_specs,
            "passed_specs": result.report.summary.passed_specs,
            "failed_specs": result.report.summary.failed_specs,
            "unfilled_specs": result.report.summary.unfilled_specs,
            "joint_passed": bool(result.report.summary.joint_passed),
        },
        "paths": {
            "run_root": str(run_root),
            "eval_dir": str(eval_dir),
            "sandbox": str(result.eval_sandbox_dir),
            "report_json": str(result.json_path),
            "report_md": str(result.md_path),
        },
    }
    (eval_dir / "eval.manifest.json").write_text(
        json.dumps(manifest, indent=2), encoding="utf-8"
    )
