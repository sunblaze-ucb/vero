"""Unit tests for axiom output parsing (no Lean invocation)."""

from __future__ import annotations

from vero.evaluation.axioms import _axiom_file_tag, _parse_axioms_output


def test_axiom_file_tag_is_slash_safe() -> None:
    assert _axiom_file_tag("Json.Proof.Utils/Seq") == "Json_Proof_Utils_Seq"


def test_parse_clean_proof() -> None:
    out = "'BankLedger.Proof.prove_create_exists' does not depend on any axioms\n"
    [r] = _parse_axioms_output(out, ["prove_create_exists"])
    assert r.status == "clean"
    assert r.axioms == []


def test_parse_standard_only() -> None:
    out = "'prove_x' depends on axioms: [Classical.choice, propext, Quot.sound]\n"
    [r] = _parse_axioms_output(out, ["prove_x"])
    assert r.status == "clean"
    assert "Classical.choice" in r.axioms


def test_parse_sorry() -> None:
    out = "'prove_x' depends on axioms: [propext, sorryAx]\n"
    [r] = _parse_axioms_output(out, ["prove_x"])
    assert r.status == "uses_sorry"


def test_parse_user_axiom() -> None:
    out = "'prove_x' depends on axioms: [Classical.choice, myAxiom]\n"
    [r] = _parse_axioms_output(out, ["prove_x"])
    assert r.status == "uses_user_axiom"
    assert "myAxiom" in r.axioms


def test_parse_missing_theorem_is_unreported() -> None:
    # If Lean's output never mentions the theorem, leave status=missing.
    out = "'prove_y' does not depend on any axioms\n"
    [r] = _parse_axioms_output(out, ["prove_x"])
    assert r.status == "missing"


def test_matches_by_last_segment() -> None:
    # Requested by bare name; Lean reports fully qualified.
    out = (
        "'BankLedger.Proof.Account.prove_create_exists' does not depend on any axioms\n"
    )
    [r] = _parse_axioms_output(out, ["prove_create_exists"])
    assert r.status == "clean"


def test_trusted_axiom_allowlist_accepts_user_axiom() -> None:
    """A user-declared axiom listed in the allowlist grades as clean."""
    out = "'prove_x' depends on axioms: [Classical.choice, BankLedger.Core.helperAx]\n"
    trusted = frozenset({"BankLedger.Core.helperAx"})
    [r] = _parse_axioms_output(out, ["prove_x"], trusted_axioms=trusted)
    assert r.status == "clean"
    assert "BankLedger.Core.helperAx" in r.axioms


def test_trusted_axiom_allowlist_does_not_whitelist_others() -> None:
    """Axioms not in the allowlist still fail even when others are allowlisted."""
    out = "'prove_x' depends on axioms: [BankLedger.Core.helperAx, rogueAxiom]\n"
    trusted = frozenset({"BankLedger.Core.helperAx"})
    [r] = _parse_axioms_output(out, ["prove_x"], trusted_axioms=trusted)
    assert r.status == "uses_user_axiom"


def test_trusted_axiom_does_not_whitelist_sorry() -> None:
    """sorryAx is always rejected, even with trusted_axioms set."""
    out = "'prove_x' depends on axioms: [sorryAx, BankLedger.Core.helperAx]\n"
    trusted = frozenset({"BankLedger.Core.helperAx", "sorryAx"})
    [r] = _parse_axioms_output(out, ["prove_x"], trusted_axioms=trusted)
    assert r.status == "uses_sorry"


def test_parse_wrapped_axiom_list_clean() -> None:
    """Lean's pretty-printer wraps long axiom lists across multiple lines.

    The parser must read the bracketed list as a single block and not
    drop the wrapped tail (which would falsely classify the theorem as
    `missing` / `build_error`).
    """
    out = "'prove_x' depends on axioms: [Classical.choice,\n propext,\n Quot.sound]\n"
    [r] = _parse_axioms_output(out, ["prove_x"])
    assert r.status == "clean"
    assert set(r.axioms) == {"Classical.choice", "propext", "Quot.sound"}


def test_parse_wrapped_axiom_list_user_axiom() -> None:
    """A user axiom appearing after a wrap point still triggers detection."""
    out = (
        "'BankLedger.Proof.Account.prove_create_exists' depends on axioms:\n"
        "  [Classical.choice,\n"
        "   propext,\n"
        "   Quot.sound,\n"
        "   BankLedger.Core.helperAx,\n"
        "   rogueAxiom]\n"
    )
    [r] = _parse_axioms_output(out, ["prove_create_exists"])
    assert r.status == "uses_user_axiom"
    assert "rogueAxiom" in r.axioms
    assert "BankLedger.Core.helperAx" in r.axioms


def test_parse_wrapped_axiom_list_with_trusted() -> None:
    """Trusted-axiom allowlist still applies when the list wraps."""
    out = (
        "'prove_x' depends on axioms: [Classical.choice,\n"
        " propext,\n"
        " BankLedger.Core.helperAx]\n"
    )
    trusted = frozenset({"BankLedger.Core.helperAx"})
    [r] = _parse_axioms_output(out, ["prove_x"], trusted_axioms=trusted)
    assert r.status == "clean"


def test_parse_two_theorems_one_wrapped() -> None:
    """Multiple #print axioms blocks in one output, one wrapped, one not."""
    out = (
        "'prove_a' does not depend on any axioms\n"
        "'prove_b' depends on axioms: [Classical.choice,\n"
        " propext,\n"
        " Quot.sound,\n"
        " sorryAx]\n"
    )
    results = _parse_axioms_output(out, ["prove_a", "prove_b"])
    by_name = {r.theorem: r for r in results}
    assert by_name["prove_a"].status == "clean"
    assert by_name["prove_b"].status == "uses_sorry"
