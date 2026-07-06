# `vero.evaluation` — grading an artifact

Given a source benchmark and an extracted artifact, re-render a clean eval sandbox, compile it, check axioms per theorem, (codeproof) verify the joint-unsat claim, and grade each spec into one of:

`passed | unfilled | overfilled | sorry_leaked | axiom_leaked | slot_body_tainted | build_error | unpaired_sat | unsafe_keyword`.

For how to *invoke* evaluation — both at the end of a fresh generation run and as a standalone re-eval on a prior run — see [`docs/gen-eval-tutorial.md`](../../../docs/gen-eval-tutorial.md).

## The anti-cheat boundary

**The evaluator never runs against the agent's own sandbox.** Instead it builds a fresh eval sandbox from the source benchmark + artifact via `vero.generation.render.render_sandbox`, and grades that. This guarantees:

1. Frozen files (`Harness.lean`, `Bundle.lean`, `Test.lean`, `Spec/*.lean`, the root hub, `lakefile.toml`, `lean-toolchain`, `manifest.json`) come from the source benchmark, not the agent. Any tampering the agent did is silently dropped.
2. `artifact.extras` (agent-added markers outside the expected schedule) are **not** rendered — they never reach the evaluator.
3. Given the same `(benchmark_dir, artifact, mode)`, the rendered sandbox is byte-identical. Runs are reproducible.

## Algorithm

1. **Render** — `render_sandbox(benchmark_dir, artifact, eval_sandbox_dir, mode)` rebuilds a fresh project and overlays the artifact's slots onto the matching marker pairs. Missing slots keep the materialize-time default (`sorry`); extras are dropped.
2. **Stage 0 — Hygiene pre-pass** (`hygiene.check_unsafe_keyword`) — whole-word `\bunsafe\b` scan over every agent-editable file (the set of `file` paths in `artifact.slots`). Comment-stripped: literal `unsafe` in a prose comment is fine. Any hit voids the run: `build_ok=False`, Stage 1/2/joint all skipped, every spec grades `unsafe_keyword`, report marks `impl_broken=True` with the offending file(s).
3. **Stage 1 — Lake build** `<root_package>.Harness`. Transitively compiles every `Impl/*.lean`, `Bundle.lean`, and `Spec/*.lean` that `canonical : RepoImpl` depends on. Failure short-circuits the evaluator into `impl_broken`: every spec grades `build_error`, no partial credit, stage 2 is skipped (`canonical` can't be constructed so nothing downstream is meaningful).
4. **Stage 2 — per-module axiom check** — for each module, write `eval/AxiomCheck_<root_package>_Proof_<Module>.lean` with `#print axioms <thm>` per expected theorem, then `lake lean` it. Parse the output into `clean | uses_sorry | uses_user_axiom | build_error | missing`. Per-module files mean a broken module doesn't cascade across modules: a failing theorem in A doesn't block B's grading. (Intra-module cascade is inherent to Lean — `.olean` is all-or-nothing.) Curator-declared `manifest.trusted_axioms` are unioned with the standard trio (`Classical.choice`, `propext`, `Quot.sound`) when classifying, so proofs depending on a declared helper grade `clean`.
5. **Joint rerender** (codeproof only) — read the `!solution specs=[…]` list and the `!benchmark proof` body; render `joint_unsat <specs> by <body>` in a fresh `eval/JointCheck.lean`; compile. Status: `no_claim | duplicate | bad_list | build_error | sorry | user_axiom | ok`. The agent's `!benchmark claim` block is **discarded** — the evaluator regenerates the macro invocation from scratch so the claim content cannot lie about what is being proved.
6. **Grade** per spec:
   - `proof` mode: exactly one of `{prove_<S>, disprove_<S>}` filled, axiom-clean → `passed`.
   - `codeproof` mode: exactly one of `{prove_<S>, unsat_<S>, sat_<S>}` filled, axiom-clean → `passed`. **Caveat:** `sat_<S>` only counts when `<S>` appears in a verified joint-unsat `!solution`; lone `sat_<S>` is `unpaired_sat` (not passed). This is the primary anti-gaming rule.
   - Filled but `uses_sorry` axiom → `sorry_leaked`.
   - Filled but `uses_user_axiom` → `axiom_leaked`.
   - Filled slot body contains an `axiom` / `admit` token → `slot_body_tainted` (short-circuits before compile).
   - Filled but file didn't compile → `build_error`.
   - More than one stub filled → `overfilled`.
   - No stubs filled → `unfilled`.

## Modules

| File | Responsibility |
|---|---|
| `lake.py` | `lake build` / `lake lean` wrappers with timeouts. Captures stdout+stderr. |
| `axioms.py` | Axiom-check file emission + `#print axioms` parser. One file per module to avoid cascade. |
| `hygiene.py` | Pre-build hygiene checks over agent-editable files. Currently: `unsafe` keyword detector. |
| `joint_rerender.py` | Codeproof-only: extract `!solution specs` + `!benchmark proof` body → fresh `eval/JointCheck.lean`, compile, classify. |
| `grade.py` | `SpecStatus` literal (incl. `unpaired_sat`), `GradeSummary` (incl. `unpaired_sat_specs`), per-spec aggregation. |
| `report.py` | `EvaluationReport` → JSON + Markdown. Surfaces per-spec status + summary + per-theorem axiom list + joint status. |
| `runner.py` | `run_evaluation(benchmark_dir, artifact, mode, eval_sandbox_dir, report_dir, ...)`. Render → build → axiom check → joint rerender → grade. Called by `vero.cli_dispatch`. |

## Anti-cheat details

- **`!benchmark claim` is discarded** (codeproof joint). The LLM's local claim only has to keep the sandbox compile-clean; the grader regenerates the macro invocation from `!solution` + `!benchmark proof`.
- **Duplicate specs in `!solution`** → `duplicate`. No faked arity.
- **Non-standard axioms** → `uses_user_axiom` → `axiom_leaked`. The standard trio `Classical.choice`, `propext`, `Quot.sound` (plus the implicit `sorryAx` which is reported separately as `uses_sorry`) are allowed; anything else fails the theorem unless it appears in `manifest.trusted_axioms`.
- **Lone `sat_<S>` is rejected** with `unpaired_sat`. Rationale: `∃ impl : RepoImpl, spec_<S> impl` is trivially provable for any non-contradictory spec by exhibiting an ad-hoc `RepoImpl` bundle — it proves nothing about the agent's own `Impl/*.lean` bodies. Only the combination of `sat_<S>` paired with a verified joint-unsat `!solution` naming `<S>` is informative, because that asserts `S` is individually satisfiable but not jointly with the other named specs.
- **Slot-body taint check** — `axiom` / `admit` tokens in a filled slot body fail fast with `slot_body_tainted` before compilation runs.
- **Frozen-file tampering is dropped at render time.** The agent cannot sneak in a spec change by editing `Spec/*.lean`.

## Fixture

`tests/fixtures/tiny_unsat/` is a 3-spec hand-crafted benchmark used by the eval tests. It exercises:

- `unsat_<S>` grading (one spec is individually unsat).
- Joint-unsat rerender happy path (two specs jointly unsat, each individually sat).
- `duplicate` rejection when the `!solution` list repeats.
- `unpaired_sat` degradation when `sat_<S>` is filled without a verified joint.

See `tests/evaluation/test_tiny_unsat_fixture.py` for the pre-baked proofs + assertions.
