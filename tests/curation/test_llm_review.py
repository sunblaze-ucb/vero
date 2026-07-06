"""Unit tests for the LLM-review dispatcher."""

from __future__ import annotations

import asyncio
from pathlib import Path

import pytest

from vero.curation.validation import validate_benchmark
from vero.curation.validation.llm_review import (
    LLM_REVIEW_CHECKS,
    ReviewRequest,
    find_review_check_specs_path,
    load_review_check_specs,
    load_review_memory,
    parse_runner_reply,
    promote_memory_candidates,
    render_memory_update_suggestions,
    render_rule_checks_for_prompt,
    run_llm_reviews,
    run_llm_reviews_async,
)
from vero.curation.validation.llm_runner import (
    CODEX_LLM_REVIEW_MODEL,
    CurationAgentLLMReviewRunner,
    build_review_prompt,
)
from vero.curation.validation.types import CheckResult, Finding

REPO_ROOT = Path(__file__).parent.parent.parent
REFERENCE = REPO_ROOT / "reference" / "BankLedger"


# ─── parse_runner_reply ──────────────────────────────────────


def test_parse_runner_reply_happy_path() -> None:
    reply = """Here is the review.

```json
{
  "name": "idiom",
  "status": "pass",
  "details": [
    {"severity": "info", "message": "Impl matches the reference shape.", "location": null}
  ]
}
```"""
    r = parse_runner_reply(reply, "idiom")
    assert r.name == "idiom"
    assert r.status == "pass"
    assert len(r.details) == 1
    assert r.details[0].severity == "info"


def test_parse_runner_reply_uses_last_json_block() -> None:
    reply = (
        '```json\n{"name":"wrong","status":"fail","details":[]}\n```\n'
        "\n"
        "Final answer:\n"
        '```json\n{"name":"idiom","status":"warn","details":[]}\n```'
    )
    r = parse_runner_reply(reply, "idiom")
    assert r.status == "warn"


def test_parse_runner_reply_no_json() -> None:
    r = parse_runner_reply("just some prose without a json block", "idiom")
    assert r.status == "fail"
    assert any("no ```json block" in f.message for f in r.details)


def test_parse_runner_reply_malformed_json() -> None:
    r = parse_runner_reply("```json\n{not valid}\n```", "idiom")
    assert r.status == "fail"
    assert any("malformed" in f.message for f in r.details)


def test_parse_runner_reply_defaults_unknown_status() -> None:
    reply = '```json\n{"name":"idiom","status":"catastrophic","details":[]}\n```'
    r = parse_runner_reply(reply, "idiom")
    assert r.status == "fail"  # unknown statuses fall back to fail


# ─── run_llm_reviews dispatch ─────────────────────────────────


def test_run_llm_reviews_skipped_when_no_runner() -> None:
    results = run_llm_reviews(REFERENCE, runner=None)
    assert results == {}


def test_run_llm_reviews_invokes_for_each_check() -> None:
    calls: list[str] = []

    def fake_runner(req: ReviewRequest) -> str:
        calls.append(req.check_name)
        return (
            f'```json\n{{"name":"{req.check_name}","status":"pass","details":[]}}\n```'
        )

    results = run_llm_reviews(REFERENCE, runner=fake_runner)
    assert set(results.keys()) == set(LLM_REVIEW_CHECKS)
    assert set(calls) == set(LLM_REVIEW_CHECKS)
    for name, check in results.items():
        assert check.status == "pass"
        assert check.name == name


def test_run_llm_reviews_only_subset() -> None:
    def fake_runner(req: ReviewRequest) -> str:
        return (
            f'```json\n{{"name":"{req.check_name}","status":"pass","details":[]}}\n```'
        )

    results = run_llm_reviews(
        REFERENCE, runner=fake_runner, only=("idiom", "test_meaningfulness")
    )
    assert set(results.keys()) == {"idiom", "test_meaningfulness"}


def test_trusted_boundary_is_builtin_review_check() -> None:
    seen: list[tuple[str, str, str]] = []

    def fake_runner(req: ReviewRequest) -> str:
        seen.append((req.check_name, req.check_description, req.check_prompt))
        return (
            f'```json\n{{"name":"{req.check_name}","status":"pass","details":[]}}\n```'
        )

    results = run_llm_reviews(REFERENCE, runner=fake_runner, only=("trusted_boundary",))

    assert "trusted_boundary" in LLM_REVIEW_CHECKS
    assert results["trusted_boundary"].status == "pass"
    assert seen[0][0] == "trusted_boundary"
    assert "external-runtime boundaries" in seen[0][1]
    assert "manifest-scored API" in seen[0][2]


def test_run_llm_reviews_surfaces_runner_exceptions() -> None:
    def bad_runner(req: ReviewRequest) -> str:
        raise RuntimeError("oops")

    results = run_llm_reviews(REFERENCE, runner=bad_runner, only=("idiom",))
    assert results["idiom"].status == "fail"
    assert any("oops" in f.message for f in results["idiom"].details)


def test_run_llm_reviews_passes_memory_excerpt(tmp_path: Path) -> None:
    memory = tmp_path / "validation_memory.md"
    memory.write_text("Known lesson: check manifest/spec drift.\n")
    seen: list[tuple[Path | None, str]] = []

    def fake_runner(req: ReviewRequest) -> str:
        seen.append((req.memory_path, req.memory_excerpt))
        return (
            f'```json\n{{"name":"{req.check_name}","status":"pass","details":[]}}\n```'
        )

    run_llm_reviews(
        REFERENCE,
        runner=fake_runner,
        only=("repo_issue_taxonomy",),
        memory_path=memory,
    )
    assert seen == [(memory, "Known lesson: check manifest/spec drift.\n")]


def test_run_llm_reviews_custom_check_spec(tmp_path: Path) -> None:
    checks = tmp_path / "checks.yaml"
    checks.write_text(
        """
checks:
  - name: piggybank_shim_boundary
    description: Check that shims do not prove PiggyBank business facts.
    prompt: Inspect trusted ConCert assumptions and PiggyBank specs.
""",
        encoding="utf-8",
    )
    seen: list[tuple[str, str, str]] = []

    def fake_runner(req: ReviewRequest) -> str:
        seen.append((req.check_name, req.check_description, req.check_prompt))
        return (
            f'```json\n{{"name":"{req.check_name}","status":"pass","details":[]}}\n```'
        )

    results = run_llm_reviews(
        REFERENCE,
        runner=fake_runner,
        only=("piggybank_shim_boundary",),
        check_specs_path=checks,
    )

    assert results["piggybank_shim_boundary"].status == "pass"
    assert seen == [
        (
            "piggybank_shim_boundary",
            "Check that shims do not prove PiggyBank business facts.",
            "Inspect trusted ConCert assumptions and PiggyBank specs.",
        )
    ]


def test_run_llm_reviews_auto_discovers_benchmark_check_specs(
    tmp_path: Path,
) -> None:
    benchmark = tmp_path / "Demo"
    spec_dir = benchmark / ".vero"
    spec_dir.mkdir(parents=True)
    checks = spec_dir / "validation_checks.yaml"
    checks.write_text(
        """
checks:
  - name: repo_local_check
    description: Check a repo-local invariant.
    prompt: Read the repo-local source map before judging.
""",
        encoding="utf-8",
    )
    seen: list[tuple[str, str, str]] = []

    def fake_runner(req: ReviewRequest) -> str:
        seen.append((req.check_name, req.check_description, req.check_source))
        return (
            f'```json\n{{"name":"{req.check_name}","status":"pass","details":[]}}\n```'
        )

    results = run_llm_reviews(
        benchmark,
        runner=fake_runner,
        only=("repo_local_check",),
    )

    assert find_review_check_specs_path(benchmark) == checks
    assert results["repo_local_check"].status == "pass"
    assert seen == [
        (
            "repo_local_check",
            "Check a repo-local invariant.",
            str(checks),
        )
    ]


def test_load_review_check_specs_rejects_bad_name(tmp_path: Path) -> None:
    checks = tmp_path / "checks.yaml"
    checks.write_text(
        "checks:\n  - name: 'bad name'\n    description: invalid\n",
        encoding="utf-8",
    )

    with pytest.raises(ValueError, match="invalid LLM review check name"):
        load_review_check_specs(checks)


def test_run_llm_reviews_async_invokes_runner() -> None:
    calls: list[str] = []

    async def fake_runner(req: ReviewRequest) -> str:
        calls.append(req.check_name)
        return (
            f'```json\n{{"name":"{req.check_name}","status":"pass","details":[]}}\n```'
        )

    results = asyncio.run(
        run_llm_reviews_async(REFERENCE, runner=fake_runner, only=("idiom",))
    )
    assert calls == ["idiom"]
    assert results["idiom"].status == "pass"


def test_render_rule_checks_for_prompt() -> None:
    rendered = render_rule_checks_for_prompt(
        {
            "guards": CheckResult(
                "guards",
                "warn",
                [Finding("warn", "missing API guard", "Demo/Test.lean")],
            )
        }
    )
    assert '"guards"' in rendered
    assert "missing API guard" in rendered


def test_build_review_prompt_names_skill_and_contract() -> None:
    req = ReviewRequest(
        check_name="repo_issue_taxonomy",
        benchmark_path=REFERENCE,
        reference_path=REFERENCE,
        memory_excerpt="Known lesson: tests can mention constants only.",
        rule_checks_json='{"guards":{"status":"warn","details":[]}}',
        check_description="Summarize repo-level quality issues.",
        check_prompt="Return candidates that can become memory.",
    )
    prompt = build_review_prompt(req)
    assert "Use the `vero-validate` skill" in prompt
    assert "check_name: `repo_issue_taxonomy`" in prompt
    assert "Known lesson" in prompt
    assert '"guards"' in prompt
    assert "Summarize repo-level quality issues" in prompt
    assert "Return candidates that can become memory" in prompt
    assert "do not edit files" in prompt


def test_curation_llm_review_runner_forces_codex_gpt55(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    seen: dict[str, object] = {}

    async def fake_call_agent(**kwargs: object) -> tuple[list[str], str | None]:
        seen.update(kwargs)
        return (
            [
                '```json\n{"name":"idiom","status":"pass","details":[]}\n```',
            ],
            None,
        )

    monkeypatch.setattr(
        "vero.curation.validation.llm_runner.call_agent",
        fake_call_agent,
    )
    runner = CurationAgentLLMReviewRunner(
        permission_mode="acceptEdits",
        max_turns=3,
        codex_auth_mode="local",
        codex_sandbox_mode="workspace-write",
        codex_network_access=True,
        codex_timeout_seconds=123,
        codex_model_reasoning_effort="high",
    )
    req = ReviewRequest(
        check_name="idiom",
        benchmark_path=REFERENCE,
        reference_path=REFERENCE,
    )
    reply = asyncio.run(runner(req))
    assert "```json" in reply
    assert seen["agent_kind"] == "codex"
    assert seen["model"] == CODEX_LLM_REVIEW_MODEL
    assert seen["codex_auth_mode"] == "local"
    assert seen["codex_sandbox_mode"] == "workspace-write"
    assert seen["codex_network_access"] is True
    assert seen["codex_timeout_seconds"] == 123
    assert seen["codex_model_reasoning_effort"] == "high"


def test_load_review_memory_uses_default_repowide_path(tmp_path: Path) -> None:
    bench = tmp_path / "bench"
    bench.mkdir()
    memory_dir = tmp_path / ".vero"
    memory_dir.mkdir()
    memory = memory_dir / "validation_memory.md"
    memory.write_text("repo lesson\n")

    path, excerpt = load_review_memory(bench)
    assert path == memory
    assert excerpt == "repo lesson\n"


def test_render_memory_update_suggestions_keeps_notable_findings() -> None:
    rendered = render_memory_update_suggestions(
        "demo",
        {
            "repo_issue_taxonomy": CheckResult(
                "repo_issue_taxonomy",
                "warn",
                [
                    Finding(
                        "warn",
                        "Deserializer stubs arrays/objects.",
                        "Demo/Impl/Parser.lean:12",
                    )
                ],
            )
        },
    )
    assert "Deserializer stubs arrays/objects" in rendered
    assert "repo_issue_taxonomy" in rendered
    assert "- [ ] id=repo_issue_taxonomy-1 target=memory" in rendered


def test_promote_memory_candidates_checked_only_and_dedupe(tmp_path: Path) -> None:
    candidates = tmp_path / "memory_candidates.md"
    memory = tmp_path / "validation_memory.md"
    candidates.write_text(
        "\n".join(
            [
                "# Validation Memory Candidates - demo",
                "",
                '- [x] id=repo_issue_taxonomy-1 target=memory severity=warn location="Spec.lean:1" :: Parser object path is stubbed.',
                '- [ ] id=repo_issue_taxonomy-2 target=memory severity=warn location="" :: Unchecked candidate.',
                "",
            ]
        ),
        encoding="utf-8",
    )

    count = promote_memory_candidates(candidates, memory, timestamp="2026-05-24")
    count_again = promote_memory_candidates(candidates, memory, timestamp="2026-05-24")
    text = memory.read_text(encoding="utf-8")

    assert count == 1
    assert count_again == 0
    assert "Parser object path is stubbed" in text
    assert "Unchecked candidate" not in text


# ─── validate_benchmark integration ───────────────────────────


def test_validate_benchmark_with_llm_runner() -> None:
    def fake_runner(req: ReviewRequest) -> str:
        return (
            f'```json\n{{"name":"{req.check_name}","status":"pass","details":[]}}\n```'
        )

    report = validate_benchmark(REFERENCE, skip_build=True, llm_runner=fake_runner)
    assert report.overall in {"pass", "warn"}
    assert set(report.llm_review.keys()) == set(LLM_REVIEW_CHECKS)
    for check in report.llm_review.values():
        assert check.status == "pass"


def test_validate_benchmark_warn_on_llm_fail() -> None:
    def failing_runner(req: ReviewRequest) -> str:
        return (
            f'```json\n{{"name":"{req.check_name}","status":"fail",'
            f'"details":[{{"severity":"error","message":"nope","location":null}}]}}\n```'
        )

    report = validate_benchmark(REFERENCE, skip_build=True, llm_runner=failing_runner)
    # Rule-based all pass; LLM fail promotes overall to warn (not fail).
    assert report.overall == "warn"
    # But blockers are rule-based only.
    assert not report.blockers


def test_validate_benchmark_to_dict_includes_llm_review() -> None:
    def fake_runner(req: ReviewRequest) -> str:
        return (
            f'```json\n{{"name":"{req.check_name}","status":"pass","details":[]}}\n```'
        )

    report = validate_benchmark(REFERENCE, skip_build=True, llm_runner=fake_runner)
    d = report.to_dict()
    assert "llm_review" in d
    assert set(d["llm_review"].keys()) == set(LLM_REVIEW_CHECKS)
    assert "rule_checks" in d
