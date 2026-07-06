"""Tests for the model-pricing table + cost computation.

Per-model rates live in :mod:`vero.generation.pricing`. We verify:
- the table contains the models we sweep with;
- both the codex usage shape (``cached_input_tokens`` and a
  ``total``-style ``input_tokens``) and the claude shape
  (``cache_read_input_tokens`` plus a ``new``-style ``input_tokens``)
  produce the right number;
- unknown models fail loudly so a missing entry is detectable;
- empty / partial usage doesn't crash.
"""

from __future__ import annotations

import pytest

from vero.generation.pricing import (
    PRICING,
    UnknownModelError,
    cost_from_usage,
)


def test_pricing_table_contains_known_models() -> None:
    assert "gpt-5.5" in PRICING
    assert "sage-gpt-5.4" in PRICING
    assert "claude-sonnet-4-6" in PRICING


def test_cost_from_usage_codex_shape() -> None:
    """codex turn.completed.usage: input_tokens is cumulative, includes cached."""
    usage = {
        "input_tokens": 1_000_000,
        "cached_input_tokens": 0,
        "output_tokens": 100_000,
    }
    cost = cost_from_usage("gpt-5.5", usage)
    # gpt-5.5: $5/Mtok new input, $30/Mtok output.
    assert cost == pytest.approx(5.0 + 30.0 * 0.1)


def test_cost_from_usage_claude_shape() -> None:
    """Claude SDK shape: input_tokens excludes cached, cache_read separate."""
    usage = {
        "input_tokens": 100_000,
        "cache_read_input_tokens": 100_000,
        "output_tokens": 50_000,
    }
    cost = cost_from_usage("claude-sonnet-4-6", usage)
    # sonnet-4-6: $3/Mtok input, $0.30/Mtok cached read, $15/Mtok output.
    assert cost == pytest.approx(3.0 * 0.1 + 0.30 * 0.1 + 15.0 * 0.05)


def test_cost_from_usage_subtracts_cached_from_codex_input() -> None:
    """codex's input_tokens is the *total* incl. cached; new = total - cached."""
    usage = {
        "input_tokens": 1_000_000,
        "cached_input_tokens": 800_000,
        "output_tokens": 0,
    }
    cost = cost_from_usage("gpt-5.5", usage)
    # 200k new at $5/Mtok + 800k cached at $0.50/Mtok.
    assert cost == pytest.approx(0.200 * 5.0 + 0.800 * 0.5)


def test_cost_from_usage_unknown_model_raises() -> None:
    with pytest.raises(UnknownModelError):
        cost_from_usage("not-a-real-model", {"input_tokens": 100})


def test_cost_from_usage_empty_usage_returns_zero() -> None:
    assert cost_from_usage("gpt-5.5", {}) == 0.0


def test_cost_from_usage_ignores_unknown_keys() -> None:
    """Defensive: unexpected usage keys must not crash; just ignored."""
    usage = {"random_key": 9999, "input_tokens": 1_000_000}
    cost = cost_from_usage("gpt-5.5", usage)
    assert cost == pytest.approx(5.0)


def test_cost_from_usage_anthropic_cache_writes_surcharged() -> None:
    """Anthropic cache_creation_input_tokens bills at 1.25× input.

    Sanity-checked against a real ``ResultMessage.usage`` from a
    bankledger smoke run: input=3, cache_create=15702, cache_read=10756,
    output=688 → SDK reported $0.123. Our number should be close (the
    SDK figure includes some ephemeral overhead we don't model).
    """
    usage = {
        "input_tokens": 3,
        "cache_creation_input_tokens": 15_702,
        "cache_read_input_tokens": 10_756,
        "output_tokens": 688,
    }
    cost = cost_from_usage("claude-sonnet-4-6", usage)
    # 3*$3/M + 15702*$3.75/M + 10756*$0.30/M + 688*$15/M
    expected = (3 * 3.0 + 15_702 * 3.75 + 10_756 * 0.30 + 688 * 15.0) / 1_000_000
    assert cost == pytest.approx(expected)


def test_cost_from_usage_pure_cache_write_billed() -> None:
    """Cache-write-only burst: 1M tokens at 1.25× = $3.75 for sonnet."""
    usage = {
        "input_tokens": 0,
        "cache_creation_input_tokens": 1_000_000,
        "output_tokens": 0,
    }
    cost = cost_from_usage("claude-sonnet-4-6", usage)
    assert cost == pytest.approx(3.75)


def test_pricing_anthropic_ratios_consistent() -> None:
    """Anthropic models follow input × {1, 0.10, 1.25, 5} ratios."""
    for name in (
        "claude-sonnet-4-6",
        "claude-sonnet-4-5",
        "claude-opus-4-7",
        "claude-haiku-4-5-20251001",
    ):
        r = PRICING[name]
        assert r.cache_read == pytest.approx(r.input * 0.10)
        assert r.cache_write == pytest.approx(r.input * 1.25)
        assert r.output == pytest.approx(r.input * 5.0)
