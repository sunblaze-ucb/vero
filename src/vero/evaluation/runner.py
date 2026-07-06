"""EvaluationRunner — render a fresh sandbox from an artifact, then grade it.

The evaluator never runs against the agent's own sandbox. It builds a **clean** eval sandbox from ``benchmark_dir`` + ``artifact`` (see ``vero.generation.render.render_sandbox``) and does all its work there. This is the anti-cheat boundary: frozen files come from the source benchmark, only marker-slot bodies come from the agent.

Flow:

1. ``render_sandbox`` → fresh Lean project at ``eval_sandbox_dir`` with the agent's bodies overlaid.
2. **Stage 1** — ``lake build <root>.Harness``. Compiles every ``Impl/``, ``Bundle``, ``Spec/`` transitively. On failure the submission grades ``impl_broken`` (every spec → ``build_error``); no partial credit.
3. **Stage 2** — per-module axiom check (one ``AxiomCheck_*.lean`` per ``Proof/<Module>.lean``). Each file imports exactly one proof module, so broken theorems in A don't block grading for B. Each theorem is classified as ``clean | uses_sorry | uses_user_axiom | build_error | missing``. Intra-module cascade is inherent (Lean doesn't emit ``.olean`` if any declaration in the file fails).
4. Joint rerender (codeproof only) — re-render + compile the ``joint_unsat`` claim from ``!solution`` + ``!benchmark proof``.
5. ``grade_specs`` → per-spec statuses + summary.
6. Write ``report.{json,md}`` into ``report_dir``.
"""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from typing import Literal

from loguru import logger

from vero.evaluation.axioms import AxiomCheckResult, check_axioms
from vero.evaluation.grade import grade_specs
from vero.evaluation.hygiene import check_implemented_by, check_unsafe_keyword
from vero.evaluation.joint_rerender import JointRerenderResult, rerender_joint
from vero.evaluation.lake import lake_build
from vero.evaluation.report import EvaluationReport, write
from vero.generation.benchmark import Benchmark
from vero.generation.extractor import Artifact
from vero.generation.render import render_sandbox

Mode = Literal["proof", "codeproof"]


def _lean_module_suffix(module_name: str) -> str:
    return module_name.replace("/", ".")


@dataclass
class EvaluationRunResult:
    report: EvaluationReport
    json_path: Path
    md_path: Path
    eval_sandbox_dir: Path


def run_evaluation(
    *,
    benchmark_dir: Path,
    artifact: Artifact,
    mode: Mode,
    eval_sandbox_dir: Path,
    report_dir: Path | None = None,
    lake_timeout: int = 600,
) -> EvaluationRunResult:
    """Render a fresh sandbox + compile + grade.

    Parameters
    ----------
    benchmark_dir:
        Source benchmark (contains ``manifest.json``). Frozen files come
        from here.
    artifact:
        Extracted ``Artifact``. Only slots with ``found=True`` and a
        non-default body are overlaid; extras are dropped.
    mode:
        Must match ``artifact.mode``.
    eval_sandbox_dir:
        Where the fresh, agent-filtered sandbox is rebuilt. Will be
        wiped and repopulated — do not point this at the agent's
        working sandbox.
    report_dir:
        Where ``report.{json,md}`` go. Defaults to
        ``eval_sandbox_dir.parent / "eval_report"``.
    """
    benchmark_dir = Path(benchmark_dir).resolve()
    eval_sandbox_dir = Path(eval_sandbox_dir).resolve()
    if report_dir is None:
        report_dir = eval_sandbox_dir.parent / "eval_report"
    report_dir = Path(report_dir).resolve()
    report_dir.mkdir(parents=True, exist_ok=True)

    # 1) Render fresh sandbox from artifact.
    logger.info(
        "rendering eval sandbox at {} from benchmark {} + artifact ({} slots, "
        "{} extras dropped)",
        eval_sandbox_dir,
        benchmark_dir,
        sum(1 for s in artifact.slots if s.found),
        len(artifact.extras),
    )
    render_sandbox(benchmark_dir, artifact, eval_sandbox_dir, mode=mode, overwrite=True)

    bench = Benchmark(eval_sandbox_dir)
    kinds = ("prove", "disprove") if mode == "proof" else ("prove", "unsat", "sat")
    trusted = frozenset(bench.trusted_axioms) if bench.trusted_axioms else None

    # Stage 0 — global hygiene pre-pass. Any agent-editable file with the
    # whole-word ``unsafe`` token, or any agent-editable ``Impl/`` file using the
    # ``@[implemented_by]`` attribute (the spec-oracle reward hack), voids the run
    # (``build_ok=False``, every spec → ``unsafe_keyword`` / ``impl_oracle``).
    # Done before Stage 1 so we don't spend compile time on a doomed run.
    editable_files = sorted({s.file for s in artifact.slots})
    unsafe_check = check_unsafe_keyword(eval_sandbox_dir, editable_files)
    impl_oracle_check = check_implemented_by(eval_sandbox_dir, editable_files)
    axioms: list = []
    joint: JointRerenderResult | None = None
    joint_specs: tuple[str, ...] = ()
    joint_ok = False
    impl_broken = False
    impl_broken_reason = ""

    # Resolve which void (if any) fires. ``unsafe`` takes precedence.
    void_status: str | None = None
    void_reason = ""
    void_tail = ""
    if unsafe_check.detected:
        void_status, void_reason = "unsafe_keyword", unsafe_check.reason
        void_tail = "(skipped — unsafe keyword detected)"
    elif impl_oracle_check.detected:
        void_status, void_reason = "impl_oracle", impl_oracle_check.reason
        void_tail = "(skipped — @[implemented_by] detected in agent impl)"

    if void_status is not None:
        logger.warning("stage 0 hygiene: {}", void_reason)
        build_ok = False
        # Synthesize per-theorem ``build_error`` placeholders so the report JSON keeps its per-theorem axiom_checks slot populated. The grader labels every spec with ``void_status`` regardless of these entries.
        for m in bench.iter_modules():
            for spec in m.specs:
                for k in kinds:
                    axioms.append(
                        AxiomCheckResult(
                            theorem=f"{k}_{spec.removeprefix('spec_')}",
                            status="build_error",
                            notes=f"{void_status} detected; compile skipped",
                        )
                    )
        specs, summary = grade_specs(
            bench,
            artifact,
            axioms,
            mode=mode,
            joint_specs=joint_specs,
            joint_ok=joint_ok,
            voided_status=void_status,  # type: ignore[arg-type]
            voided_reason=void_reason,
        )
        report = EvaluationReport(
            benchmark_id=bench.benchmark_id,
            mode=mode,
            sandbox_dir=str(eval_sandbox_dir),
            build_ok=build_ok,
            build_tail=void_tail,
            specs=specs,
            summary=summary,
            joint=None,
            axiom_checks=axioms,
            impl_broken=True,
            impl_broken_reason=void_reason,
        )
        json_path = report_dir / "report.json"
        md_path = report_dir / "report.md"
        write(report, json_path, md_path)
        logger.info("wrote {} and {}", json_path, md_path)
        return EvaluationRunResult(
            report=report,
            json_path=json_path,
            md_path=md_path,
            eval_sandbox_dir=eval_sandbox_dir,
        )

    # Stage 1 — build ``<root>.Harness``. This transitively compiles every ``Impl/*.lean``, ``Bundle.lean``, and ``Spec/*.lean`` that ``canonical : RepoImpl`` depends on. If any of those fail, nothing downstream is meaningful — ``canonical`` can't be constructed, so every proof about it is vacuous. Grade zero partial credit and bail out.
    harness_target = f"{bench.root_package}.Harness"
    logger.info("stage 1: `lake build {}`", harness_target)
    harness_res = lake_build(eval_sandbox_dir, harness_target, timeout=lake_timeout)
    build_ok = harness_res.ok

    if not build_ok:
        impl_broken = True
        impl_broken_reason = (
            f"`{harness_target}` failed to compile — upstream "
            f"(Impl / Bundle / Spec / Harness) is broken. "
            f"No partial credit. Tail: {harness_res.combined[-300:]}"
        )
        logger.warning("stage 1 failed — impl_broken, skipping per-module checks")
        # Synthesize build_error axiom-check results for every expected theorem so the grader produces a consistent ``build_error`` row per spec.
        for m in bench.iter_modules():
            for spec in m.specs:
                for k in kinds:
                    axioms.append(
                        AxiomCheckResult(
                            theorem=f"{k}_{spec.removeprefix('spec_')}",
                            status="build_error",
                            notes="upstream (Harness) compile failed",
                        )
                    )
    else:
        # Stage 2 — per-module axiom check. Each module's AxiomCheck file imports exactly one proof module, so a broken theorem in A doesn't block B's grading. Intra-module cascade is inherent (Lean's .olean isn't emitted when any declaration in the file fails).
        for m in bench.iter_modules():
            names = [f"{k}_{s.removeprefix('spec_')}" for s in m.specs for k in kinds]
            if not names:
                continue
            logger.info("axiom check: module={} ({} theorems)", m.name, len(names))
            sub, _ = check_axioms(
                eval_sandbox_dir,
                names,
                proof_import=f"{bench.root_package}.Proof.{_lean_module_suffix(m.name)}",
                timeout=lake_timeout,
                trusted_axioms=trusted,
            )
            axioms.extend(sub)

        # 4) Joint rerender (codeproof only).
        if mode == "codeproof":
            joint = rerender_joint(eval_sandbox_dir, artifact, timeout=lake_timeout)
            joint_specs = joint.specs
            joint_ok = joint.status == "ok"
            logger.info(
                "joint rerender status={} specs={}",
                joint.status,
                list(joint_specs),
            )

    # 5) Grade + report.
    specs, summary = grade_specs(
        bench,
        artifact,
        axioms,
        mode=mode,
        joint_specs=joint_specs,
        joint_ok=joint_ok,
    )

    report = EvaluationReport(
        benchmark_id=bench.benchmark_id,
        mode=mode,
        sandbox_dir=str(eval_sandbox_dir),
        build_ok=build_ok,
        build_tail=harness_res.combined[-1200:],
        specs=specs,
        summary=summary,
        joint=joint,
        axiom_checks=axioms,
        impl_broken=impl_broken,
        impl_broken_reason=impl_broken_reason,
    )

    json_path = report_dir / "report.json"
    md_path = report_dir / "report.md"
    write(report, json_path, md_path)
    logger.info("wrote {} and {}", json_path, md_path)

    return EvaluationRunResult(
        report=report,
        json_path=json_path,
        md_path=md_path,
        eval_sandbox_dir=eval_sandbox_dir,
    )
