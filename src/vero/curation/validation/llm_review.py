"""LLM-review subagent dispatch for the validate stage.

Semantic checks that complement the deterministic rule-based checks in
:mod:`.checks`.
"""

from __future__ import annotations

import json
import re
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Awaitable, Callable, Protocol

import yaml

from .types import CheckResult, Finding, Status


@dataclass(frozen=True)
class ReviewCheckSpec:
    """One LLM-review check definition."""

    name: str
    description: str
    prompt: str = ""
    source: str = "builtin"


BUILTIN_LLM_REVIEW_CHECK_SPECS = (
    ReviewCheckSpec(
        "spec_intent_alignment",
        "Spec bodies should match their natural-language descriptions or plan intent.",
    ),
    ReviewCheckSpec(
        "idiom",
        "Impl, Bundle, and Harness code should be idiomatic Lean and match the benchmark paradigm.",
    ),
    ReviewCheckSpec(
        "test_meaningfulness",
        "#guard tests should be non-trivial, cover the API surface, and include boundary cases.",
    ),
    ReviewCheckSpec(
        "review_annotations",
        "!curation @review annotations should be specific, nearby, and not stale template text.",
    ),
    ReviewCheckSpec(
        "spec_completeness",
        "The spec set should cover each API's observable behavior, including obvious failure paths.",
    ),
    ReviewCheckSpec(
        "repo_issue_taxonomy",
        "Summarize recurring repo-specific quality issues that should feed memory, rules, or follow-up tasks.",
    ),
    ReviewCheckSpec(
        "trusted_boundary",
        "Trusted, opaque, axiom, and external-runtime boundaries should be explicit, minimal, non-scored unless justified, and reflected in specs/tests without hiding benchmark-specific behavior.",
        prompt=(
            "Inspect manifest.json, .vero/plan.json if present, Impl files, Bundle/Harness, and representative Spec/Test files. "
            "Pass only when trusted/opaque/external declarations are isolated from scored Bundle APIs unless the plan explicitly justifies the boundary; specs mention the boundary rather than becoming self-referential or vacuous; tests do not fake external results; and no benchmark-specific axiom/opaque helper is used to prove ordinary API behavior. "
            "Warn for promotion-quality gaps such as non-executable trusted callbacks, missing trusted-boundary tests, over-broad opaque context, or unclear manifest/bundle metadata. "
            "Fail when a trusted declaration silently replaces scored behavior, appears as a manifest-scored API without review, or introduces unreviewed benchmark-specific axioms/sorries."
        ),
    ),
)

LLM_REVIEW_CHECKS = tuple(spec.name for spec in BUILTIN_LLM_REVIEW_CHECK_SPECS)

DEFAULT_MEMORY_BASENAMES = (
    "validation_memory.md",
    "repo_quality_audit_takeaways.md",
)

DEFAULT_CHECK_SPEC_BASENAMES = (
    "validation_checks.yaml",
    "llm_review_checks.yaml",
)


@dataclass
class ReviewRequest:
    """Inputs handed to a subagent for one LLM review."""

    check_name: str
    benchmark_path: Path
    reference_path: Path | None
    memory_path: Path | None = None
    memory_excerpt: str = ""
    rule_checks_json: str = ""
    check_description: str = ""
    check_prompt: str = ""
    check_source: str = "builtin"


class LLMReviewRunner(Protocol):
    """Callable that invokes a subagent and returns raw reply text."""

    def __call__(self, request: ReviewRequest) -> str: ...


class AsyncLLMReviewRunner(Protocol):
    """Async callable that invokes a subagent and returns raw reply text."""

    def __call__(self, request: ReviewRequest) -> Awaitable[str]: ...


_JSON_FENCE_RE = re.compile(r"```json\s*\n(.+?)\n```", re.DOTALL)
_CHECK_NAME_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_:-]*$")


def _default_memory_candidates(benchmark_path: Path) -> list[Path]:
    return [
        *(benchmark_path / ".vero" / name for name in DEFAULT_MEMORY_BASENAMES),
        *(benchmark_path.parent / ".vero" / name for name in DEFAULT_MEMORY_BASENAMES),
    ]


def _default_check_spec_candidates(benchmark_path: Path) -> list[Path]:
    return [
        *(benchmark_path / ".vero" / name for name in DEFAULT_CHECK_SPEC_BASENAMES),
        *(
            benchmark_path.parent / ".vero" / name
            for name in DEFAULT_CHECK_SPEC_BASENAMES
        ),
    ]


def find_review_check_specs_path(benchmark_path: Path) -> Path | None:
    """Return the first benchmark-local LLM-review check spec file, if any."""
    return next(
        (
            path
            for path in _default_check_spec_candidates(benchmark_path)
            if path.exists()
        ),
        None,
    )


def load_review_memory(
    benchmark_path: Path,
    *,
    memory_path: Path | None = None,
    max_chars: int = 12_000,
) -> tuple[Path | None, str]:
    """Load prior validation lessons for LLM judges."""
    candidates = (
        [memory_path]
        if memory_path is not None
        else _default_memory_candidates(benchmark_path)
    )
    for path in candidates:
        if path is None or not path.exists():
            continue
        text = path.read_text(encoding="utf-8")
        if len(text) > max_chars:
            text = text[-max_chars:]
        return path, text
    return None, ""


def render_rule_checks_for_prompt(
    rule_checks: dict[str, CheckResult] | None,
    *,
    max_details_per_check: int = 8,
    max_message_chars: int = 1200,
) -> str:
    """Serialize deterministic findings into compact JSON for LLM review."""
    if not rule_checks:
        return "{}"
    payload: dict[str, dict] = {}
    for name, check in rule_checks.items():
        payload[name] = {
            "status": check.status,
            "details": [
                {
                    "severity": f.severity,
                    "message": f.message[:max_message_chars],
                    "location": f.location,
                }
                for f in check.details[:max_details_per_check]
            ],
        }
    return json.dumps(payload, indent=2)


def load_review_check_specs(path: Path | None) -> tuple[ReviewCheckSpec, ...]:
    """Load built-in plus YAML/JSON-defined LLM-review check specs."""
    if path is None:
        return BUILTIN_LLM_REVIEW_CHECK_SPECS
    data = yaml.safe_load(path.read_text(encoding="utf-8"))
    if isinstance(data, list):
        raw_checks = data
    elif isinstance(data, dict):
        raw_checks = data.get("checks", [])
    else:
        raw_checks = []

    specs = list(BUILTIN_LLM_REVIEW_CHECK_SPECS)
    for raw in raw_checks:
        if not isinstance(raw, dict):
            continue
        name = str(raw.get("name", "")).strip()
        description = str(raw.get("description", "")).strip()
        prompt = str(raw.get("prompt", "")).strip()
        if not name or not description:
            continue
        if not _CHECK_NAME_RE.match(name):
            raise ValueError(f"invalid LLM review check name {name!r}")
        specs.append(
            ReviewCheckSpec(
                name=name,
                description=description,
                prompt=prompt,
                source=str(path),
            )
        )
    return tuple(specs)


def _review_spec_map(
    benchmark_path: Path,
    check_specs_path: Path | None,
) -> dict[str, ReviewCheckSpec]:
    if check_specs_path is None:
        check_specs_path = find_review_check_specs_path(benchmark_path)
    return {spec.name: spec for spec in load_review_check_specs(check_specs_path)}


def parse_runner_reply(reply: str, check_name: str) -> CheckResult:
    """Extract the trailing ```json block and convert to a CheckResult."""
    matches = _JSON_FENCE_RE.findall(reply)
    if not matches:
        return CheckResult(
            name=check_name,
            status="fail",
            details=[
                Finding(
                    "error",
                    "LLM reply contained no ```json block (subagent output contract violation)",
                )
            ],
        )
    try:
        payload = json.loads(matches[-1])
    except json.JSONDecodeError as e:
        return CheckResult(
            name=check_name,
            status="fail",
            details=[Finding("error", f"LLM JSON malformed: {e}")],
        )

    name = payload.get("name", check_name)
    raw_status = payload.get("status", "fail")
    status: Status = raw_status if raw_status in ("pass", "warn", "fail") else "fail"
    details: list[Finding] = []
    for item in payload.get("details", []):
        details.append(
            Finding(
                severity=item.get("severity", "info"),
                message=item.get("message", ""),
                location=item.get("location"),
            )
        )
    return CheckResult(name=name, status=status, details=details)


def _build_review_request(
    *,
    name: str,
    spec: ReviewCheckSpec,
    benchmark_path: Path,
    reference_path: Path | None,
    memory_path: Path | None,
    rule_checks: dict[str, CheckResult] | None,
) -> ReviewRequest:
    loaded_memory_path, memory_excerpt = load_review_memory(
        benchmark_path,
        memory_path=memory_path,
    )
    return ReviewRequest(
        check_name=name,
        benchmark_path=benchmark_path,
        reference_path=reference_path,
        memory_path=loaded_memory_path,
        memory_excerpt=memory_excerpt,
        rule_checks_json=render_rule_checks_for_prompt(rule_checks),
        check_description=spec.description,
        check_prompt=spec.prompt,
        check_source=spec.source,
    )


def run_llm_reviews(
    benchmark_path: Path,
    *,
    runner: LLMReviewRunner | Callable[[ReviewRequest], str] | None,
    reference_path: Path | None = None,
    memory_path: Path | None = None,
    only: tuple[str, ...] | None = None,
    rule_checks: dict[str, CheckResult] | None = None,
    check_specs_path: Path | None = None,
) -> dict[str, CheckResult]:
    """Run LLM reviews and return ``{check_name: CheckResult}``."""
    if runner is None:
        return {}
    specs = _review_spec_map(benchmark_path, check_specs_path)
    targets = only if only else tuple(specs)

    results: dict[str, CheckResult] = {}
    for name in targets:
        spec = specs.get(name)
        if spec is None:
            results[name] = CheckResult(
                name=name,
                status="fail",
                details=[Finding("error", f"unknown LLM review check {name!r}")],
            )
            continue
        request = _build_review_request(
            name=name,
            spec=spec,
            benchmark_path=benchmark_path,
            reference_path=reference_path,
            memory_path=memory_path,
            rule_checks=rule_checks,
        )
        try:
            reply = runner(request)
        except Exception as exc:  # noqa: BLE001
            results[name] = CheckResult(
                name=name,
                status="fail",
                details=[Finding("error", f"LLM runner raised: {exc!r}")],
            )
            continue
        results[name] = parse_runner_reply(reply, name)
    return results


async def run_llm_reviews_async(
    benchmark_path: Path,
    *,
    runner: AsyncLLMReviewRunner | Callable[[ReviewRequest], Awaitable[str]] | None,
    reference_path: Path | None = None,
    memory_path: Path | None = None,
    only: tuple[str, ...] | None = None,
    rule_checks: dict[str, CheckResult] | None = None,
    check_specs_path: Path | None = None,
) -> dict[str, CheckResult]:
    """Async variant of :func:`run_llm_reviews` for production agent calls."""
    if runner is None:
        return {}
    specs = _review_spec_map(benchmark_path, check_specs_path)
    targets = only if only else tuple(specs)

    results: dict[str, CheckResult] = {}
    for name in targets:
        spec = specs.get(name)
        if spec is None:
            results[name] = CheckResult(
                name=name,
                status="fail",
                details=[Finding("error", f"unknown LLM review check {name!r}")],
            )
            continue
        request = _build_review_request(
            name=name,
            spec=spec,
            benchmark_path=benchmark_path,
            reference_path=reference_path,
            memory_path=memory_path,
            rule_checks=rule_checks,
        )
        try:
            reply = await runner(request)
        except Exception as exc:  # noqa: BLE001
            results[name] = CheckResult(
                name=name,
                status="fail",
                details=[Finding("error", f"LLM runner raised: {exc!r}")],
            )
            continue
        results[name] = parse_runner_reply(reply, name)
    return results


def render_memory_update_suggestions(
    benchmark_id: str,
    results: dict[str, CheckResult],
) -> str:
    """Render warn/error LLM findings as human-reviewable promotion candidates."""
    lines = [
        f"# Validation Memory Candidates - {benchmark_id}",
        "",
        "These are suggestions only. Check `[x]` on lines that should be promoted, "
        "then run `python -m vero.curation promote-memory <candidates.md> <memory.md>`.",
        "",
    ]
    any_finding = False
    for name, check in results.items():
        notable = [f for f in check.details if f.severity in {"warn", "error"}]
        if not notable:
            continue
        any_finding = True
        lines.append(f"## {name}")
        lines.append("")
        for i, finding in enumerate(notable, start=1):
            loc = finding.location or ""
            message = " ".join(finding.message.split())
            lines.append(
                f"- [ ] id={name}-{i} target=memory severity={finding.severity} "
                f"location={json.dumps(loc)} :: {message}"
            )
        lines.append("")
    if not any_finding:
        lines.append("- No warn/error LLM findings to promote.")
        lines.append("")
    return "\n".join(lines)


_PROMOTION_RE = re.compile(
    r"^- \[(?P<checked>[xX])\]\s+"
    r"id=(?P<id>\S+)\s+target=(?P<target>\S+)\s+severity=(?P<severity>\S+)\s+"
    r"location=(?P<location>\"(?:\\.|[^\"])*\")\s+::\s+(?P<message>.+)$"
)


def promote_memory_candidates(
    candidates_path: Path,
    memory_path: Path,
    *,
    timestamp: str | None = None,
) -> int:
    """Append checked memory candidates to a durable memory file."""
    if not candidates_path.exists():
        raise FileNotFoundError(candidates_path)
    timestamp = timestamp or datetime.now(timezone.utc).date().isoformat()
    existing = memory_path.read_text(encoding="utf-8") if memory_path.exists() else ""
    additions: list[str] = []
    for line in candidates_path.read_text(encoding="utf-8").splitlines():
        match = _PROMOTION_RE.match(line)
        if not match:
            continue
        loc = json.loads(match.group("location"))
        location = f" location={loc}" if loc else ""
        entry = (
            f"- {timestamp} [{match.group('severity')}] {match.group('id')}"
            f"{location}: {match.group('message')}"
        )
        if entry not in existing and entry not in additions:
            additions.append(entry)

    if not additions:
        return 0
    memory_path.parent.mkdir(parents=True, exist_ok=True)
    prefix = existing.rstrip()
    header = f"## Promoted Validation Lessons - {timestamp}"
    text = "\n".join([header, "", *additions, ""])
    if prefix:
        memory_path.write_text(prefix + "\n\n" + text, encoding="utf-8")
    else:
        memory_path.write_text("# Validation Memory\n\n" + text, encoding="utf-8")
    return len(additions)


__all__ = [
    "LLM_REVIEW_CHECKS",
    "BUILTIN_LLM_REVIEW_CHECK_SPECS",
    "AsyncLLMReviewRunner",
    "LLMReviewRunner",
    "ReviewCheckSpec",
    "ReviewRequest",
    "find_review_check_specs_path",
    "load_review_check_specs",
    "load_review_memory",
    "parse_runner_reply",
    "promote_memory_candidates",
    "render_rule_checks_for_prompt",
    "render_memory_update_suggestions",
    "run_llm_reviews",
    "run_llm_reviews_async",
]
