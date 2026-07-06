"""Production LLM-review runner for curation validation."""

from __future__ import annotations

from dataclasses import dataclass

from vero.curation.agent import REPO_ROOT, call_agent
from vero.curation.validation.llm_review import ReviewRequest

CODEX_LLM_REVIEW_MODEL = "gpt-5.5"


@dataclass
class CurationAgentLLMReviewRunner:
    """Invoke Codex/gpt-5.5 for one validate-stage LLM review."""

    permission_mode: str
    max_turns: int
    model: str = CODEX_LLM_REVIEW_MODEL
    api_key: str | None = None
    api_base_url: str | None = None
    codex_auth_mode: str = "api"
    codex_sandbox_mode: str = "danger-full-access"
    codex_network_access: bool = False
    codex_timeout_seconds: int = 1800
    codex_model_reasoning_effort: str | None = None

    def __post_init__(self) -> None:
        if self.model != CODEX_LLM_REVIEW_MODEL:
            raise ValueError(
                "validate-stage LLM review must use Codex model "
                f"{CODEX_LLM_REVIEW_MODEL!r}, got {self.model!r}"
            )

    async def __call__(self, request: ReviewRequest) -> str:
        prompt = build_review_prompt(request)
        texts, _session_id = await call_agent(
            model=CODEX_LLM_REVIEW_MODEL,
            permission_mode=self.permission_mode,
            prompt=prompt,
            tools=["Read", "Grep", "Glob", "Bash"],
            max_turns=self.max_turns,
            api_key=self.api_key,
            api_base_url=self.api_base_url,
            agent_kind="codex",
            codex_auth_mode=self.codex_auth_mode,
            codex_sandbox_mode=self.codex_sandbox_mode,
            codex_timeout_seconds=self.codex_timeout_seconds,
            codex_network_access=self.codex_network_access,
            codex_model_reasoning_effort=self.codex_model_reasoning_effort,
        )
        return "\n\n".join(texts)


def build_review_prompt(request: ReviewRequest) -> str:
    """Build the single-check prompt consumed by the curation agent."""
    reference_path = request.reference_path or (REPO_ROOT / "reference" / "BankLedger")
    memory_section = (
        request.memory_excerpt
        if request.memory_excerpt
        else "(no prior validation memory was found)"
    )
    memory_path = str(request.memory_path) if request.memory_path else "(none)"
    rule_checks = request.rule_checks_json or "{}"
    check_description = (
        request.check_description
        if request.check_description
        else "(see the vero-validate skill for this built-in check)"
    )
    check_prompt = (
        request.check_prompt
        if request.check_prompt
        else "(no additional check-specific instructions)"
    )
    return f"""Use the `vero-validate` skill before doing this review.

You are running the LLM-review half of the curation validate stage. Run exactly one semantic review check and do not edit files.

## Inputs

- benchmark_path: `{request.benchmark_path}`
- reference_path: `{reference_path}`
- check_name: `{request.check_name}`
- memory_path: `{memory_path}`
- check_source: `{request.check_source}`

## Check Definition

Description:

```text
{check_description}
```

Additional check-specific instructions:

```text
{check_prompt}
```

## Deterministic Rule-Check Findings

```json
{rule_checks}
```

## Prior Memory Excerpt

```markdown
{memory_section}
```

## Task

Follow the `vero-validate` skill for `check_name`. Read only the files needed for this check. Use `reference_path` as the canonical benchmark shape. Use the deterministic rule-check findings as context, especially for `repo_issue_taxonomy`.

Return a single `CheckResult` JSON object as the final fenced ```json block. The JSON object must have:

- `name`: exactly `{request.check_name}`
- `status`: `pass`, `warn`, or `fail`
- `details`: a list of findings with `severity`, `message`, and `location`

Keep the result concrete and cite file locations when possible.
"""


__all__ = [
    "CODEX_LLM_REVIEW_MODEL",
    "CurationAgentLLMReviewRunner",
    "build_review_prompt",
]
