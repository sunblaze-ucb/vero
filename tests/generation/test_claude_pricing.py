"""Tests for ClaudeAgent cost-source resolution.

ClaudeAgent.``_resolve_costs`` returns ``(canonical, sdk, token)``:

- ``canonical`` is what surfaces as ``RunOutcome.total_cost_usd`` and what
  the iterate harness uses for ``iterate.budget_usd``. SDK is preferred —
  Anthropic's billing includes overhead (cache-write surcharges,
  extended-context tiers, subscription metering) that our pricing table
  doesn't fully model. The token-based number ran 3–9× under the SDK
  number in smoke runs, so trusting tokens would silently break the cap.
- ``token`` is :func:`pricing.cost_from_usage` of ``usage`` — preserved
  for cross-check / analysis even when not canonical.
- ``sdk`` is the SDK's ``ResultMessage.total_cost_usd``, passed through.
"""

from __future__ import annotations

import pytest

from vero.generation.agents.claude import ClaudeAgent


def test_resolve_costs_prefers_sdk_when_available() -> None:
    """Canonical = SDK figure; token figure stays computable for cross-check."""
    agent = ClaudeAgent(model="claude-sonnet-4-6")
    sdk_cost = 0.4242
    usage = {
        "input_tokens": 100_000,
        "cache_read_input_tokens": 100_000,
        "output_tokens": 50_000,
    }
    canonical, sdk_kept, token = agent._resolve_costs(sdk_cost, usage)
    assert canonical == pytest.approx(0.4242)
    assert sdk_kept == pytest.approx(0.4242)
    # Token figure: 3*0.1 + 0.30*0.1 + 15*0.05 = 1.08
    assert token == pytest.approx(1.08)


def test_resolve_costs_unknown_model_still_uses_sdk() -> None:
    """Unknown model → token=None, but canonical is still SDK number."""
    agent = ClaudeAgent(model="not-a-real-model")
    sdk_cost = 0.4242
    usage = {"input_tokens": 100, "output_tokens": 100}
    canonical, sdk_kept, token = agent._resolve_costs(sdk_cost, usage)
    assert canonical == pytest.approx(0.4242)
    assert sdk_kept == pytest.approx(0.4242)
    assert token is None


def test_resolve_costs_no_usage_keeps_sdk() -> None:
    """Empty usage: canonical is SDK; token is None."""
    agent = ClaudeAgent(model="claude-sonnet-4-6")
    canonical, sdk_kept, token = agent._resolve_costs(0.123, {})
    assert canonical == pytest.approx(0.123)
    assert sdk_kept == pytest.approx(0.123)
    assert token is None


def test_resolve_costs_no_sdk_no_usage_returns_none() -> None:
    """No SDK + no usage → all three None."""
    agent = ClaudeAgent(model="claude-sonnet-4-6")
    canonical, sdk_kept, token = agent._resolve_costs(None, {})
    assert canonical is None
    assert sdk_kept is None
    assert token is None


def test_resolve_costs_no_sdk_falls_back_to_tokens() -> None:
    """SDK didn't report (defensive — shouldn't happen on the API path):
    canonical falls back to the token figure so the budget cap still has
    something to bind on."""
    agent = ClaudeAgent(model="claude-sonnet-4-6")
    usage = {"input_tokens": 1_000_000, "output_tokens": 0}
    canonical, sdk_kept, token = agent._resolve_costs(None, usage)
    assert canonical == pytest.approx(3.0)
    assert sdk_kept is None
    assert token == pytest.approx(3.0)
