"""Per-model pricing table + token-based cost computation.

Used to turn an agent's reported token usage into a $-cost figure that
can be fed to ``iterate.budget_usd`` for caps and to ``agent_events.jsonl``
for analysis. Numbers are USD per 1M tokens, sourced from the prior
sweep's measured costs (see ``eval_results/20260501-22python-codeproof.md``)
or the model card when no measurement is available.

Update this table whenever a new model joins the rotation. Unknown models
raise :class:`UnknownModelError` so missing entries surface loudly rather
than silently zeroing out the cost.

Two usage shapes are accepted without normalisation:

- codex ``turn.completed.usage`` — ``input_tokens`` is cumulative and
  *includes* any cached portion; cached portion is in ``cached_input_tokens``.
- Anthropic SDK ``ResultMessage.usage`` — ``input_tokens`` is the new
  (uncached) input; cached reads come in ``cache_read_input_tokens``.

The two shapes are disambiguated by which cached-key alias is present:
``cached_input_tokens`` (codex) means ``input_tokens`` is *cumulative* so
new = total − cached; ``cache_read_input_tokens`` (Anthropic) means
``input_tokens`` is already the new-input count and we just bill cached
separately. The dispatch lives in :func:`cost_from_usage`.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Mapping


class UnknownModelError(KeyError):
    """Raised when ``cost_from_usage`` sees a model with no pricing entry."""


@dataclass(frozen=True)
class ModelRate:
    """USD per 1M tokens.

    ``input`` and ``output`` are always required. ``cache_read`` and
    ``cache_write`` are optional: ``None`` means "not separately
    published by this provider" — :func:`cost_from_usage` falls back to
    the ``input`` rate in that case.

    Anthropic publishes both: ``cache_read`` ≈ input × 0.10 (90%
    discount) and ``cache_write`` ≈ input × 1.25 (25% surcharge for
    the 5m TTL tier). OpenAI / codex doesn't separately bill cache
    writes — they're rolled into the ``input_tokens`` total. Many
    OpenRouter-routed open-weight providers publish only ``cache_read``
    (or nothing at all); leaving the unknown rate as ``None`` is more
    honest than guessing.
    """

    input: float
    output: float
    cache_read: float | None = None
    cache_write: float | None = None


def _claude_rate(input_rate: float) -> ModelRate:
    """Anthropic standard ratios per their public pricing:
    cache_read = input × 0.10 (90% discount on hits),
    cache_write_5m = input × 1.25 (25% surcharge on creates).
    """
    return ModelRate(
        input=input_rate,
        output=input_rate * 5.0,  # sonnet/haiku/opus all bill output at 5× input
        cache_read=input_rate * 0.10,
        cache_write=input_rate * 1.25,
    )


PRICING: Mapping[str, ModelRate] = {
    # Codex / OpenAI rotation, measured against a LiteLLM
    # proxy. ``cache_write`` is None because codex's
    # ``turn.completed.usage`` doesn't separate cache-creation from
    # input — those tokens already land in ``input_tokens``.
    "gpt-5.5": ModelRate(input=5.0, output=30.0, cache_read=0.50),
    "sage-gpt-5.4": ModelRate(input=3.0, output=15.0, cache_read=0.30),
    # Claude rotation. Anthropic public pricing — input × {1, 0.10, 1.25, 5}.
    "claude-sonnet-5": _claude_rate(3.0),
    "claude-sonnet-4-6": _claude_rate(3.0),
    "claude-sonnet-4-5": _claude_rate(3.0),
    "claude-opus-4-8": _claude_rate(5.0),
    "claude-opus-4-7": _claude_rate(15.0),
    "claude-haiku-4-5-20251001": _claude_rate(1.0),
    # OpenRouter-routed open-weight models. Rates from the OpenRouter
    # model cards (input + output always; cache_read only when the
    # provider publishes a separate hit rate; cache_write left None
    # since none of these publish a creation surcharge).
    "z-ai/glm-5.1": ModelRate(input=1.40, output=4.40),
    "minimax/minimax-m2.7": ModelRate(input=0.30, output=1.20, cache_read=0.06),
    "moonshotai/kimi-k2.6": ModelRate(input=1.20, output=4.50, cache_read=0.20),
    "deepseek/deepseek-v4-pro": ModelRate(input=2.10, output=4.40, cache_read=0.20),
}


_INPUT_KEY = "input_tokens"
_OUTPUT_KEY = "output_tokens"
# Reasoning models bill their hidden reasoning tokens at the OUTPUT rate.
# codex reports them separately from ``output_tokens`` (which counts only the
# visible completion), so they must be added in or cost is undercounted.
_REASONING_KEY = "reasoning_output_tokens"
# codex: input_tokens is cumulative including cached → subtract.
_CODEX_CACHED_KEY = "cached_input_tokens"
# anthropic: input_tokens already excludes cached → don't subtract.
_ANTHROPIC_CACHE_READ_KEY = "cache_read_input_tokens"
# anthropic only: cache writes (5m TTL) — surcharged.
_ANTHROPIC_CACHE_WRITE_KEY = "cache_creation_input_tokens"


def _as_int(usage: Mapping[str, int | float], key: str) -> int:
    v = usage.get(key)
    return int(v) if isinstance(v, (int, float)) else 0


def normalize_model(model: str) -> str:
    """Map a backend-qualified model id to a pricing-table key.

    The eval rotation passes provider-prefixed ids (e.g. Bedrock's
    ``openai.gpt-5.5``, cross-region ``us.openai.gpt-5.5``, or an
    OpenRouter ``openai/gpt-5.5``). The pricing table keys on the bare
    model name, so strip a leading ``us.`` region prefix and a single
    ``<provider>.`` / ``<provider>/`` vendor prefix, then try the table.
    Returns the input unchanged if no alias applies.
    """
    m = model.strip()
    if m in PRICING:
        return m
    # Drop a cross-region inference prefix like ``us.`` / ``eu.`` / ``apac.``.
    for region in ("us.", "eu.", "apac.", "us-gov."):
        if m.startswith(region):
            m = m[len(region) :]
            break
    if m in PRICING:
        return m
    # Drop a single vendor prefix (``openai.gpt-5.5`` → ``gpt-5.5``,
    # ``openai/gpt-5.5`` → ``gpt-5.5``). Keep vendor-qualified OpenRouter
    # keys (``z-ai/glm-5.1``) intact by only stripping when the bare tail
    # is itself a table key.
    for sep in (".", "/"):
        if sep in m:
            tail = m.split(sep, 1)[1]
            if tail in PRICING:
                return tail
    return model


def cost_from_usage(model: str, usage: Mapping[str, int | float]) -> float:
    """Compute USD cost for one agent run from its ``usage`` dict.

    Empty usage → 0.0. Unknown model → :class:`UnknownModelError`.

    The ``model`` is normalized (:func:`normalize_model`) so a
    provider-prefixed id (``openai.gpt-5.5``) resolves to its bare
    pricing key (``gpt-5.5``).

    When ``rate.cache_read`` or ``rate.cache_write`` is ``None`` (the
    provider doesn't publish a separate rate), the corresponding tokens
    are billed at the ``input`` rate — a conservative fallback that
    won't underestimate cost.
    """
    if not usage:
        return 0.0
    rate = PRICING.get(normalize_model(model))
    if rate is None:
        raise UnknownModelError(model)

    raw_input = _as_int(usage, _INPUT_KEY)
    # Reasoning tokens are billed at the output rate; add them to visible output.
    output = _as_int(usage, _OUTPUT_KEY) + _as_int(usage, _REASONING_KEY)

    # Disambiguate codex vs anthropic shapes.
    codex_cached = _as_int(usage, _CODEX_CACHED_KEY)
    anth_cache_read = _as_int(usage, _ANTHROPIC_CACHE_READ_KEY)
    anth_cache_write = _as_int(usage, _ANTHROPIC_CACHE_WRITE_KEY)

    if codex_cached:
        # codex: input_tokens is cumulative; cache_writes folded into input rate.
        cache_read_tok = codex_cached
        cache_write_tok = 0
        new_input = max(0, raw_input - cache_read_tok)
    else:
        # anthropic (or any shape with separate cache reads/writes).
        cache_read_tok = anth_cache_read
        cache_write_tok = anth_cache_write
        new_input = raw_input

    cache_read_rate = rate.cache_read if rate.cache_read is not None else rate.input
    cache_write_rate = rate.cache_write if rate.cache_write is not None else rate.input

    return (
        new_input * rate.input / 1_000_000
        + cache_read_tok * cache_read_rate / 1_000_000
        + cache_write_tok * cache_write_rate / 1_000_000
        + output * rate.output / 1_000_000
    )
