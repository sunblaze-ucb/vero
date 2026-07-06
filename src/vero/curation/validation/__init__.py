"""Rule-based validation for curated Lean 4 benchmarks.

Entry point: :func:`validate_benchmark`. See :mod:`.types` for the
result shape (matches the ``validate.json`` schema in
``docs/pipeline-schema.md``).

Typical use:

.. code-block:: python

    from pathlib import Path
    from vero.curation.validation import validate_benchmark

    report = validate_benchmark(Path("reference/BankLedger"))
    print(report.overall)
    for name, check in report.rule_checks.items():
        print(f"  {name}: {check.status}")
"""

from __future__ import annotations

from pathlib import Path
from typing import Callable

from .checks import run_rule_checks
from .llm_review import (
    LLMReviewRunner,
    ReviewRequest,
    render_memory_update_suggestions,
    run_llm_reviews,
    run_llm_reviews_async,
)
from .types import CheckResult, Finding, Severity, Status, ValidationReport


def validate_benchmark(
    benchmark_path: Path,
    *,
    skip_build: bool = False,
    build_timeout: int = 300,
    llm_runner: LLMReviewRunner | Callable[[ReviewRequest], str] | None = None,
    reference_path: Path | None = None,
) -> ValidationReport:
    """Run all rule-based checks on the benchmark at ``benchmark_path``.

    ``benchmark_path`` must point to the Lean project directory containing
    ``manifest.json``, ``lakefile.toml``, and the Lean tree.

    Set ``skip_build=True`` to skip ``lake build`` (fast path for
    editor-time validation or CI that builds separately).

    Pass ``llm_runner`` to also run the LLM-review half (see
    :mod:`.llm_review`). Defaults to ``None`` — LLM-review is skipped
    and only rule-based checks populate the report.
    """
    rule_results = run_rule_checks(
        benchmark_path,
        skip_build=skip_build,
        build_timeout=build_timeout,
    )
    llm_results = run_llm_reviews(
        benchmark_path,
        runner=llm_runner,
        reference_path=reference_path,
    )
    return ValidationReport(
        benchmark_path=benchmark_path,
        rule_checks=rule_results,
        llm_review=llm_results,
    )


__all__ = [
    "CheckResult",
    "Finding",
    "LLMReviewRunner",
    "ReviewRequest",
    "Severity",
    "Status",
    "ValidationReport",
    "render_memory_update_suggestions",
    "run_llm_reviews",
    "run_llm_reviews_async",
    "validate_benchmark",
]
