"""Validation result types."""

from __future__ import annotations

from dataclasses import dataclass, field
from pathlib import Path
from typing import Literal

Severity = Literal["info", "warn", "error"]
Status = Literal["pass", "warn", "fail", "skipped"]


@dataclass
class Finding:
    """One observation from a check."""

    severity: Severity
    message: str
    location: str | None = None


@dataclass
class CheckResult:
    """Outcome of a single check."""

    name: str
    status: Status
    details: list[Finding] = field(default_factory=list)

    @property
    def is_pass(self) -> bool:
        return self.status == "pass"


@dataclass
class ValidationReport:
    """Aggregate of rule-based checks + (optional) LLM-review checks.

    ``llm_review`` may be empty — the LLM-review half is opt-in (requires
    a subagent runner). Rule-based blockers always count; LLM-review
    failures become blockers only under ``strict=True`` at eval time
    (callers inspect ``llm_review`` directly for non-strict use).
    """

    benchmark_path: Path
    rule_checks: dict[str, CheckResult] = field(default_factory=dict)
    llm_review: dict[str, CheckResult] = field(default_factory=dict)

    @property
    def overall(self) -> Status:
        statuses = [c.status for c in self.rule_checks.values()]
        # LLM-review statuses contribute to warn but not fail (unless strict).
        statuses += [c.status for c in self.llm_review.values()]
        if "fail" in [c.status for c in self.rule_checks.values()]:
            return "fail"
        if "warn" in statuses or "fail" in statuses:
            return "warn"
        return "pass"

    @property
    def blockers(self) -> list[str]:
        out = []
        for name, check in self.rule_checks.items():
            if check.status == "fail":
                for f in check.details:
                    if f.severity == "error":
                        loc = f" [{f.location}]" if f.location else ""
                        out.append(f"{name}: {f.message}{loc}")
        return out

    def to_dict(self) -> dict:
        """JSON-serializable form matching docs/pipeline-schema.md's validate.json shape."""

        def _check_to_dict(check: CheckResult) -> dict:
            return {
                "status": check.status,
                "details": [
                    {
                        "severity": f.severity,
                        "message": f.message,
                        "location": f.location,
                    }
                    for f in check.details
                ],
            }

        return {
            "version": 1,
            "overall": self.overall,
            "blockers": self.blockers,
            "rule_checks": {
                name: _check_to_dict(check) for name, check in self.rule_checks.items()
            },
            "llm_review": {
                name: _check_to_dict(check) for name, check in self.llm_review.items()
            },
        }
