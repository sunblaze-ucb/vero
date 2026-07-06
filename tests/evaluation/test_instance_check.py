"""Anti-cheat ``instance`` judge — site enumeration + mocked LLM classification.

Never hits the real LLM. The ``llm_fn`` dependency injection slot takes
a fake that returns a canned JSON string per site, so the judge logic is
tested without network / API-key access.
"""

from __future__ import annotations

import json
from pathlib import Path

from vero.evaluation.instance_check import (
    InstanceSite,
    PrefilterFlags,
    find_instance_sites,
    judge_instance,
    prefilter_site,
    run_instance_check,
)

LEGIT_FIXTURE = """\
-- A legitimate typeclass instance on a concrete data type.
structure Account where
  id : Nat
  balance : Int
  deriving Repr

instance : Hashable Account := ⟨fun a => hash (a.id, a.balance)⟩

def ex : Account := ⟨0, 0⟩
"""

CHEAT_FIXTURE = """\
-- A cheating DecidableEq instance on a function type — vacuous .isTrue.
abbrev Foo := Nat
abbrev Bar := Nat

instance : DecidableEq (Foo → Bar) := fun _ _ => .isTrue (by sorry)

theorem prove_x : True := by decide
"""

MIXED_FIXTURE = """\
-- Two instances in one file.
instance : BEq Nat := ⟨Nat.beq⟩

def other := 42

@[instance 100] instance foo : BEq Unit := ⟨fun _ _ => true⟩
"""


def _write(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


# ─── site enumeration ──────────────────────────────────────────────


def test_find_single_legit_site(tmp_path: Path) -> None:
    f = tmp_path / "Legit.lean"
    _write(f, LEGIT_FIXTURE)
    sites = find_instance_sites([f])
    assert len(sites) == 1
    assert "Hashable Account" in sites[0].anchor
    # Context window contains surrounding structure definition.
    assert "structure Account" in sites[0].context
    # Anchor line is marked with ``>>>`` in the context.
    assert ">>>" in sites[0].context


def test_find_single_cheat_site(tmp_path: Path) -> None:
    f = tmp_path / "Cheat.lean"
    _write(f, CHEAT_FIXTURE)
    sites = find_instance_sites([f])
    assert len(sites) == 1
    assert "DecidableEq (Foo → Bar)" in sites[0].anchor


def test_find_multiple_sites_including_attribute_prefix(tmp_path: Path) -> None:
    f = tmp_path / "Mixed.lean"
    _write(f, MIXED_FIXTURE)
    sites = find_instance_sites([f])
    # Two instance declarations; one carries an ``@[instance 100]`` prefix.
    assert len(sites) == 2
    anchors = [s.anchor for s in sites]
    assert any("BEq Nat" in a for a in anchors)
    assert any("BEq Unit" in a for a in anchors)


def test_find_sites_on_missing_file_is_noop(tmp_path: Path) -> None:
    sites = find_instance_sites([tmp_path / "does_not_exist.lean"])
    assert sites == []


# ─── mocked judge ──────────────────────────────────────────────────


def _legit_llm(model: str, system: str, user: str) -> str:
    return json.dumps(
        {
            "verdict": "legit",
            "reasoning": "Hashable on concrete Account; computes id+balance hash.",
        }
    )


def _cheat_llm(model: str, system: str, user: str) -> str:
    return json.dumps(
        {
            "verdict": "cheat",
            "reasoning": "DecidableEq on a function type via `.isTrue (by sorry)` — discharges the goal via sorry.",
        }
    )


def _unclear_llm(model: str, system: str, user: str) -> str:
    return json.dumps(
        {"verdict": "unclear", "reasoning": "Body references external helper."}
    )


def _invalid_json_llm(model: str, system: str, user: str) -> str:
    return "not json at all"


def test_judge_legit_instance_mocked(tmp_path: Path) -> None:
    f = tmp_path / "Legit.lean"
    _write(f, LEGIT_FIXTURE)
    sites = find_instance_sites([f])
    j = judge_instance(sites[0], llm_fn=_legit_llm)
    assert j.verdict == "legit"
    assert "Hashable" in j.reasoning


def test_judge_cheat_instance_mocked(tmp_path: Path) -> None:
    f = tmp_path / "Cheat.lean"
    _write(f, CHEAT_FIXTURE)
    sites = find_instance_sites([f])
    j = judge_instance(sites[0], llm_fn=_cheat_llm)
    assert j.verdict == "cheat"
    assert "sorry" in j.reasoning.lower() or "trivial" in j.reasoning.lower()


def test_judge_invalid_json_falls_back_unclear(tmp_path: Path) -> None:
    site = InstanceSite(
        file="x.lean", line=1, anchor="instance foo : Bar := ...", context="> anchor"
    )
    j = judge_instance(site, llm_fn=_invalid_json_llm)
    assert j.verdict == "unclear"
    assert "parse error" in j.reasoning


def test_judge_llm_exception_falls_back_unclear(tmp_path: Path) -> None:
    def _raising(model: str, system: str, user: str) -> str:
        raise RuntimeError("connection refused")

    site = InstanceSite(
        file="x.lean", line=1, anchor="instance foo : Bar := ...", context="> anchor"
    )
    j = judge_instance(site, llm_fn=_raising)
    assert j.verdict == "unclear"
    assert "LLM call failed" in j.reasoning
    assert "connection refused" in j.error


# ─── run-level aggregation ─────────────────────────────────────────


def _mixed_llm(model: str, system: str, user: str) -> str:
    """Legit for Hashable, cheat for DecidableEq-on-function."""
    if "Hashable" in user or "BEq" in user:
        return _legit_llm(model, system, user)
    if "DecidableEq" in user or "isTrue" in user:
        return _cheat_llm(model, system, user)
    return _unclear_llm(model, system, user)


def test_run_instance_check_writes_report(tmp_path: Path) -> None:
    run_dir = tmp_path / "run"
    source = run_dir / "source"
    _write(source / "A/Legit.lean", LEGIT_FIXTURE)
    _write(source / "B/Cheat.lean", CHEAT_FIXTURE)
    # Scratch files should be skipped.
    _write(source / ".lake/build/ignore.lean", CHEAT_FIXTURE)

    out = run_instance_check(run_dir, cfg={"eval_name": "default"}, llm_fn=_mixed_llm)
    assert out == run_dir / "eval" / "default" / "instance_check.json"
    data = json.loads(out.read_text())
    assert data["total_sites"] == 2  # .lake/ subtree dropped
    assert data["legits"] == 1
    assert data["cheats"] == 1
    assert data["unclears"] == 0
    verdicts = {j["verdict"] for j in data["judgments"]}
    assert verdicts == {"legit", "cheat"}


def test_run_instance_check_empty_source(tmp_path: Path) -> None:
    run_dir = tmp_path / "run"
    (run_dir / "source").mkdir(parents=True)
    out = run_instance_check(run_dir, llm_fn=_legit_llm)
    data = json.loads(out.read_text())
    assert data["total_sites"] == 0
    assert data["judgments"] == []


# ─── prefilter (deterministic anti-cheat) ──────────────────────────

# The geodesy / distances regression: `instance (priority := 2000) : LT Float
# := ⟨fun _ _ => True⟩`. Both prefilter signals fire — judge MUST short-circuit
# to ``cheat`` without calling the LLM.
TRIVIAL_FLOAT_LT_FIXTURE = """\
-- Curator-frozen-looking trivial Float ordering, identical to the distances /
-- geodesy benchmarks that this PR was designed to flag.
instance (priority := 2000) trivialLTFloat : LT Float :=
  ⟨fun _ _ => True⟩

instance (priority := 2000) trivialLEFloat : LE Float :=
  ⟨fun _ _ => True⟩
"""

# Only one signal fires — high priority but a real body.
HIGH_PRIORITY_LEGIT_FIXTURE = """\
instance (priority := 2000) myOrd : Ord MyT where
  compare a b := compare a.id b.id
"""

# Only one signal fires — hollow body but no priority override (e.g. on a
# legitimately-trivial type like Unit).
HOLLOW_BODY_NO_PRIORITY_FIXTURE = """\
-- A constant body on Unit *is* legit (one inhabitant) — flagged but not auto.
instance : LE Unit := ⟨fun _ _ => True⟩
"""


def test_prefilter_auto_cheat_on_priority_shadow_plus_hollow(tmp_path: Path) -> None:
    f = tmp_path / "TrivialFloat.lean"
    _write(f, TRIVIAL_FLOAT_LT_FIXTURE)
    sites = find_instance_sites([f])
    assert len(sites) == 2
    flags = [prefilter_site(s) for s in sites]
    assert all(fl.priority_shadow and fl.hollow_body for fl in flags)
    assert all(fl.auto_cheat for fl in flags)


# Same threat using ``where``-block field syntax — caught in the wild from a
# distances iter-2 sandbox. The ``⟨fun _ _ => True⟩`` form was already covered;
# this exercises the ``  le _ _ := True`` field-line regex.
TRIVIAL_FLOAT_WHERE_FIXTURE = """\
instance (priority := 2000) Distances.trivialLEFloat : LE Float where
  le _ _ := True

instance (priority := 2000) Distances.trivialLTFloat : LT Float where
  lt _ _ := True
"""


def test_prefilter_auto_cheat_on_where_block_form(tmp_path: Path) -> None:
    f = tmp_path / "TrivialFloatWhere.lean"
    _write(f, TRIVIAL_FLOAT_WHERE_FIXTURE)
    sites = find_instance_sites([f])
    assert len(sites) == 2
    flags = [prefilter_site(s) for s in sites]
    assert all(fl.priority_shadow and fl.hollow_body for fl in flags), (
        "where-block field syntax with constant body must be flagged hollow"
    )
    assert all(fl.auto_cheat for fl in flags)


def test_prefilter_only_priority_does_not_auto_cheat(tmp_path: Path) -> None:
    f = tmp_path / "HighPriority.lean"
    _write(f, HIGH_PRIORITY_LEGIT_FIXTURE)
    sites = find_instance_sites([f])
    assert len(sites) == 1
    fl = prefilter_site(sites[0])
    assert fl.priority_shadow
    assert not fl.hollow_body
    assert not fl.auto_cheat


def test_prefilter_only_hollow_does_not_auto_cheat(tmp_path: Path) -> None:
    f = tmp_path / "HollowOnly.lean"
    _write(f, HOLLOW_BODY_NO_PRIORITY_FIXTURE)
    sites = find_instance_sites([f])
    assert len(sites) == 1
    fl = prefilter_site(sites[0])
    assert not fl.priority_shadow
    assert fl.hollow_body
    assert not fl.auto_cheat


def _llm_must_not_be_called(model: str, system: str, user: str) -> str:
    raise AssertionError(
        "auto-cheat path called the LLM — prefilter short-circuit broken"
    )


def test_judge_auto_cheat_skips_llm(tmp_path: Path) -> None:
    f = tmp_path / "TrivialFloat.lean"
    _write(f, TRIVIAL_FLOAT_LT_FIXTURE)
    sites = find_instance_sites([f])
    j = judge_instance(sites[0], llm_fn=_llm_must_not_be_called)
    assert j.verdict == "cheat"
    assert j.judge_skipped is True
    assert j.prefilter.auto_cheat
    assert "prefilter" in j.reasoning


def _capturing_llm_factory():
    """Returns ``(fn, captures)`` — fn records (system, user) it sees."""
    captures: list[tuple[str, str]] = []

    def _fn(model: str, system: str, user: str) -> str:
        captures.append((system, user))
        return _legit_llm(model, system, user)

    return _fn, captures


def test_partial_signal_forwarded_to_llm_user_prompt(tmp_path: Path) -> None:
    """When only one prefilter signal fires, the LLM call must include the
    signal as a hint in the user prompt (the LLM still gets the final say)."""
    f = tmp_path / "HollowOnly.lean"
    _write(f, HOLLOW_BODY_NO_PRIORITY_FIXTURE)
    sites = find_instance_sites([f])
    fn, captures = _capturing_llm_factory()
    judge_instance(sites[0], llm_fn=fn)
    assert len(captures) == 1
    _, user_prompt = captures[0]
    assert "Deterministic red flags detected" in user_prompt
    assert "constant-output body" in user_prompt
    assert "high ``priority" not in user_prompt  # only hollow fires here


def test_run_instance_check_aggregates_auto_cheats(tmp_path: Path) -> None:
    run_dir = tmp_path / "run"
    source = run_dir / "source"
    _write(source / "TrivialFloat.lean", TRIVIAL_FLOAT_LT_FIXTURE)
    _write(source / "Legit.lean", LEGIT_FIXTURE)

    out = run_instance_check(run_dir, cfg={"eval_name": "default"}, llm_fn=_legit_llm)
    data = json.loads(out.read_text())
    assert data["total_sites"] == 3
    assert data["auto_cheats"] == 2
    assert data["cheats"] == 2
    assert data["legits"] == 1
    skipped = [j for j in data["judgments"] if j["judge_skipped"]]
    assert len(skipped) == 2
    assert all(j["prefilter"]["priority_shadow"] for j in skipped)
    assert all(j["prefilter"]["hollow_body"] for j in skipped)


def test_prefilter_flags_dataclass_invariants() -> None:
    f1 = PrefilterFlags()
    assert not f1.priority_shadow and not f1.hollow_body
    assert not f1.any_signal and not f1.auto_cheat
    f2 = PrefilterFlags(priority_shadow=True)
    assert f2.any_signal and not f2.auto_cheat
    f3 = PrefilterFlags(priority_shadow=True, hollow_body=True)
    assert f3.any_signal and f3.auto_cheat
