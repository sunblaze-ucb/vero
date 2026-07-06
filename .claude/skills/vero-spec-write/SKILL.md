---
name: vero-spec-write
description: Use during the spec_write stage to author specifications for translated Python (or new-source) projects in two substeps — reason about what specs should exist, then formalize them in Lean. Pair with vero-lean-pitfalls.
allowed-tools: Read, Write, Edit, Bash, Grep, Glob
---

# VCG Spec Write

The `spec_write` stage is the bridge between an executable-only translation (Impl/ files only, Spec/ files empty) and a benchmark-ready project. It runs in two substeps with a human-review gate between them.

**Reference the canonical shape** at `reference/BankLedger/`. Every spec compiles, every spec is `(impl : RepoImpl) : Prop`, every public API is referenced by ≥1 spec.

## Substep 1 — REASON

You read the translated Impl files + manifest and write `curation/spec_plan.md` proposing one or more specs per API.

**Coverage rule:** every public API must appear in ≥1 proposed spec. The mapping is captured in a Coverage table at the bottom of `spec_plan.md`.

**Non-vacuity rule:** a spec should usually constrain an implementation
through `impl.<repo_impl_field>.<api>`. Do not propose specs whose
substantive body is just `True`, non-empty output, deterministic
repetition of the same call, or a theorem-only helper fact unless the
plan explicitly marks it as a helper/non-obligation. Success-only
postconditions are not enough for partial APIs; include failure behavior
when the source has it.

**Be creative.** Look beyond per-API correctness:
- **Cross-API invariants** — `f` and `g` commute; `f` is the inverse of `g` on its image; iterating `f` preserves a measure; `merge` is associative + commutative.
- **Frame conditions** — `f x ledger` doesn't change accounts other than `x`.
- **Edge cases** — empty input, singleton, max-size, concurrent updates if the model exposes them.
- **Algebraic laws** — monoid identity, idempotence, distributivity over the underlying structure.
- **Round-trips** — decode ∘ encode = id (where it should hold); failure modes (decode of malformed input rejects).

**Format** (one section per spec):

```markdown
## spec_<descriptive_name>

- **Module:** `<ModuleName>`
- **Covers APIs:** `f`, `g`
- **Intent (NL):** one paragraph plain English.
- **Lean sketch:**
  ```lean
  def spec_<name> (impl : RepoImpl) : Prop :=
    ∀ … , …  -- pseudocode is fine
  ```
- **Notes for human:** assumptions, edge cases, alternatives.
```

If a spec needs a new helper predicate (used only inside specs), propose it under `## spec_helpers (proposed)` near the top of the plan.

End the file with a `## Coverage` table:

```markdown
| Module | API | Specs |
|---|---|---|
| Account | createAccount | spec_create_zero_balance, spec_create_exists |
| Account | closeAccount | spec_close_removes |
```

After writing the file, the stage pauses. The human edits the proposed specs in place and adds `# APPROVED` as the first non-blank line of `spec_plan.md` to release the gate.

## Substep 2 — FORMALIZE

After the human approves, you read the (potentially edited) plan back and write Lean defs into `<Project>/<Project>/Spec/<Module>.lean`.

**Hard rules** (validator-enforced):

1. Every spec is `def spec_<name> (impl : RepoImpl) : Prop := …`. The parameter name may be `_impl` if unused.
2. Spec files contain **only** `def spec_*` and `def spec_helper_*` declarations. No `theorem`, `lemma`, `example`, `axiom`, `instance`, or `!benchmark` markers.
3. Spec bodies access APIs via `impl.<repo_impl_field>.<fn>` — see `<Project>/Bundle.lean` for the field name (lowerCamelCase of the package name).
4. `spec_helper_*` defs (executable predicates referenced inside specs) live alongside the specs in the same module's Spec file, near the top.
5. Update `manifest.json::packages[].modules[].specs[]` with the bare-string names. Helpers go under the module's optional `spec_helpers[]` list.
6. For translated-source repos, record source provenance for each new
   spec in the curation report or `.vero/source_map.json`; include
   the source function/theorem/pre/postcondition that motivated it.

**Order of operations:**

1. Read every section of the approved `spec_plan.md`.
2. Group specs by module.
3. For each module, write a single `Spec/<Module>.lean` file:
   ```lean
   import <Project>.Harness

   /-! # <Project>.Spec.<Module>

   <one-paragraph module summary>

   DO NOT MODIFY — frozen curator-given content.
   -/

   /-- helper predicate (if any) -/
   def spec_helper_foo (…) : Bool := …

   /-- <NL intent for spec_x> -/
   def spec_x (impl : RepoImpl) : Prop :=
     …
   ```
4. Update `manifest.json` `specs[]` (and `spec_helpers[]` if used) for that module.
5. Run `lake build` from the project root. Iterate until clean.
6. Verify the `spec_shape` rule check passes: every listed spec is typed `(impl : RepoImpl) : Prop` and no `theorem`/`lemma`/`example` slipped in.

## Common pitfalls

- **Forgetting the bundle field name.** It's lowerCamelCase of the package name, defined in `Harness.lean`'s `RepoImpl` structure. Always read `Bundle.lean` + `Harness.lean` first.
- **Writing `Prop` body that depends on `axiom`.** Don't. The grader rejects user-introduced axioms.
- **Using `theorem` in a spec file.** Theorems live in `Proof/` (materialized later by the gen pipeline) — never in `Spec/`.
- **Ambiguous helper kind.** A boolean helper (`def spec_helper_x : … → Bool`) is fine. A `Prop`-typed helper that can't be specialized to a `RepoImpl` shouldn't claim to be a `spec_*` — name it `spec_helper_*` so the validator skips the `(impl : RepoImpl) : Prop` shape rule.
- **Skipping the coverage check.** If an API isn't in any spec, the source_coverage validator warns and the curator has to circle back.
- **Weak parser/serializer specs.** For JSON-like or codec-like repos,
  exact byte-level behavior, malformed-input rejection, buffer
  prefix/suffix preservation, and serialize/deserialize round trips are
  usually the core semantics. Specs like "output is non-empty" or
  "output begins with a quote" are not sufficient.
