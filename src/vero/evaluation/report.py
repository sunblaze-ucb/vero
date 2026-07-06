"""Evaluation report — JSON + Markdown."""

from __future__ import annotations

import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any

from vero.evaluation.axioms import AxiomCheckResult
from vero.evaluation.grade import GradeSummary, SpecResult
from vero.evaluation.joint_rerender import JointRerenderResult


@dataclass
class EvaluationReport:
    benchmark_id: str
    mode: str
    sandbox_dir: str
    build_ok: bool
    build_tail: str
    specs: list[SpecResult]
    summary: GradeSummary
    joint: JointRerenderResult | None = None
    axiom_checks: list[AxiomCheckResult] | None = None
    impl_broken: bool = False
    # True iff ``<root>/Harness.lean`` failed to compile — i.e. the
    # upstream layer (Impl / Bundle / Spec / Harness) is broken. When
    # set, every spec grades as ``build_error`` and the summary reflects
    # zero partial credit: we don't attempt per-module checks when the
    # curator-declared ``canonical`` can't even be constructed.
    impl_broken_reason: str = ""


def to_dict(r: EvaluationReport) -> dict[str, Any]:
    return {
        "benchmark_id": r.benchmark_id,
        "mode": r.mode,
        "sandbox_dir": r.sandbox_dir,
        "build": {
            "ok": r.build_ok,
            "tail": r.build_tail,
            "impl_broken": r.impl_broken,
            "impl_broken_reason": r.impl_broken_reason,
        },
        "summary": asdict(r.summary),
        "specs": [asdict(s) for s in r.specs],
        "joint": asdict(r.joint) if r.joint else None,
        "axiom_checks": (
            [asdict(a) for a in r.axiom_checks] if r.axiom_checks else None
        ),
    }


def to_json(r: EvaluationReport) -> str:
    return json.dumps(to_dict(r), indent=2)


def write(r: EvaluationReport, json_path: Path, md_path: Path | None = None) -> None:
    json_path.write_text(to_json(r), encoding="utf-8")
    if md_path is not None:
        md_path.write_text(to_markdown(r), encoding="utf-8")


def to_markdown(r: EvaluationReport) -> str:
    lines: list[str] = []
    lines.append(f"# Evaluation — `{r.benchmark_id}` (mode: `{r.mode}`)")
    lines.append("")
    lines.append("## Summary")
    lines.append("")
    s = r.summary
    build_label = "✅ ok"
    if r.impl_broken:
        build_label = f"❌ impl_broken — {r.impl_broken_reason}"
    elif not r.build_ok:
        build_label = "❌ failed"
    lines.append(f"- **Build**: {build_label}")
    lines.append(f"- **Specs passed**: {s.passed_specs} / {s.total_specs}")
    lines.append(f"- **Unfilled**: {s.unfilled_specs}")
    lines.append(f"- **Overfilled**: {s.overfilled_specs}")
    lines.append(f"- **Unpaired `sat_<S>` (rejected)**: {s.unpaired_sat_specs}")
    lines.append(f"- **Failed (sorry/axiom/tainted/build)**: {s.failed_specs}")
    if r.mode == "codeproof":
        lines.append(
            f"- **Joint-unsat**: {'✅ ok' if s.joint_passed else '—'}"
            + (f" ({r.joint.status})" if r.joint else "")
        )
    lines.append("")
    lines.append("## Per-spec results")
    lines.append("")
    lines.append("| Module | Spec | Status | Filled | Notes |")
    lines.append("|---|---|---|---|---|")
    for sr in r.specs:
        filled = ",".join(k.kind for k in sr.kinds if k.filled) or "—"
        notes = sr.notes.replace("|", "\\|") if sr.notes else ""
        lines.append(
            f"| {sr.module} | `{sr.spec}` | {sr.status} | {filled} | {notes} |"
        )
    if r.joint:
        lines.append("")
        lines.append("## Joint claim")
        lines.append("")
        lines.append(f"- Status: **{r.joint.status}**")
        if r.joint.specs:
            lines.append(f"- Specs: `{', '.join(r.joint.specs)}`")
        if r.joint.theorem_name:
            lines.append(f"- Theorem: `{r.joint.theorem_name}`")
        if r.joint.notes:
            lines.append(f"- Notes: {r.joint.notes}")
    return "\n".join(lines) + "\n"
