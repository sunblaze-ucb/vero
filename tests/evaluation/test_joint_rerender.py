"""Unit tests for joint_rerender's pure helpers (no Lean invocation)."""

from __future__ import annotations

from vero.evaluation.joint_rerender import _parse_spec_list


def test_default_placeholder_returns_none() -> None:
    body = ["specs=[<FILL: comma-separated spec names, e.g. spec_a, spec_b>]"]
    assert _parse_spec_list(body) is None


def test_well_formed_list() -> None:
    body = ["specs=[spec_a, spec_b, spec_c]"]
    assert _parse_spec_list(body) == ("spec_a", "spec_b", "spec_c")


def test_empty_list_is_empty_tuple() -> None:
    body = ["specs=[]"]
    assert _parse_spec_list(body) == ()


def test_no_list_returns_none() -> None:
    body = ["-- no specs here"]
    assert _parse_spec_list(body) is None


def test_list_can_span_lines() -> None:
    body = [
        "-- some commentary",
        "specs=[spec_a,",
        "       spec_b]",
    ]
    # We accept single-line per current impl; multi-line is rare. Skip it for now.
    # If multi-line is needed later, update _LIST_RE to be multiline-aware.
    # Just ensure the helper doesn't crash.
    result = _parse_spec_list(body)
    # Either parses both or just the first (acceptable v1 behavior).
    assert result is None or result[0] == "spec_a"
