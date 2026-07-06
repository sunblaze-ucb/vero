"""Unit tests for the python-from-benchmark-json scaffolder helpers.

Pure-function coverage: identifier casing, binder rendering, arrow-type
construction, and synthetic-plan manifest emission. The former
fixture-driven tests (which loaded ``datasets/primepy/task/benchmark.json``)
were removed together with the ``datasets/`` tree.
"""

from __future__ import annotations

from vero.curation.stages.python_from_json import (
    Api,
    BenchTest,
    Param,
    Plan,
    _render_manifest,
    camel_capitalize,
    lower_first,
)

# ─── Helpers (unit) ─────────────────────────────────────────────────


def test_camel_capitalize() -> None:
    assert camel_capitalize("factor") == "Factor"
    assert camel_capitalize("factors") == "Factors"
    assert camel_capitalize("") == ""
    assert camel_capitalize("myApi") == "MyApi"


def test_lower_first() -> None:
    assert lower_first("Primepy") == "primepy"
    assert lower_first("BankLedger") == "bankLedger"
    assert lower_first("") == ""


def test_param_render_binder() -> None:
    assert Param("x", "Int", "Explicit").render_binder() == "(x : Int)"
    assert Param("α", "Type", "Implicit").render_binder() == "{α : Type}"
    assert (
        Param("inst", "Hashable T", "Instance").render_binder() == "[inst : Hashable T]"
    )


def test_api_sig_and_arrow_type() -> None:
    a = Api(
        name="factor",
        params=(Param("num", "Int", "Explicit"),),
        ret_typ="Int",
        tests=(),
    )
    assert a.sig_name == "FactorSig"
    assert a.arrow_type == "Int → Int"

    b = Api(
        name="between",
        params=(
            Param("m", "Int", "Explicit"),
            Param("n", "Int", "Explicit"),
        ),
        ret_typ="List Int",
        tests=(),
    )
    assert b.arrow_type == "Int → Int → List Int"

    c = Api(name="x", params=(), ret_typ="Nat", tests=())
    assert c.arrow_type == "Nat"


# ─── Synthetic-plan unit (covers binder kinds + manifest emission) ──


def test_emit_with_implicit_and_instance_params() -> None:
    """Non-primepy fixture: Implicit + Instance binders are supported.

    `render_binder` is tested above; arrow_type joins `typ`s directly, so a
    mix of Implicit + Instance + Explicit should still yield a clean arrow
    chain.
    """
    a = Api(
        name="hash",
        params=(
            Param("T", "Type", "Implicit"),
            Param("inst", "Hashable T", "Instance"),
            Param("x", "T", "Explicit"),
        ),
        ret_typ="UInt64",
        tests=(BenchTest(inputs=(("x", "0"),), expected="0"),),
    )
    assert a.arrow_type == "Type → Hashable T → T → UInt64"

    # Also verify `BenchTest.render_args` skips implicit/instance binders.
    rendered = a.tests[0].render_args(a)
    assert rendered == "0", f"expected only explicit args, got {rendered!r}"

    # And a plan built around this API emits a valid manifest entry.
    plan = Plan(
        benchmark_id="toy",
        package="Toy",
        repo_impl_field="toy",
        bundle_type="ToyBundle",
        files=(),
        warnings=(),
        source_meta=None,
    )
    m = _render_manifest(plan)
    assert m["benchmark_id"] == "toy"
