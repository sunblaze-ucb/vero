---
name: vero-translate
description: Use when translating selected verified items from Dafny/Verus/Coq into a compilable Lean 4 benchmark. Scaffolds the project to the ratified bundle paradigm (Bundle.lean + structure RepoImpl + Impl/Spec/Harness/Test layout) and wraps each reference implementation body in the correct `!benchmark` marker. Pair with `vero-source-{dafny,verus,coq}`.
allowed-tools: Read, Write, Edit, Bash, Grep, Glob, Agent
---

# VCG Translate: Verified Code → Lean 4 Benchmark

Translate the selected items from the upstream source into a compilable
Lean 4 project that matches the ratified paradigm documented in
`reference/BankLedger/`. This is curation stage output: produce
`Impl/`, `Spec/`, `Harness.lean`, `Bundle.lean`, `Test.lean`, root hub,
`lakefile.toml`, `lean-toolchain`, and `manifest.json`. **Do NOT emit
`Proof/`** — that layer is materialized downstream at pre-agent-gen.

**Canonical example:** `reference/BankLedger/`. When uncertain about
marker placement, Bundle shape, manifest field names, or docstring
style, read those files directly — they are the living contract.

## When to use

- After `plan` stage has produced `.vero/plan.json` and humans have
  approved it.
- Pair with the appropriate `vero-source-{lang}` skill for per-language
  translation patterns.

## Prerequisites

- `.vero/plan.json` exists with the approved translation plan
  (schema: `docs/pipeline-schema.md`).
- Source files accessible.
- Language skill loaded.

---

## Output shape (must match `reference/BankLedger/`)

```
<Project>/                         # Lean project root
├── lakefile.toml                  # see "Lakefile" below
├── lean-toolchain                 # leanprover/lean4:v4.29.1
├── manifest.json                  # see docs/pipeline-schema.md
├── <Project>.lean                 # root hub — imports only
└── <Project>/                     # root package dir
    ├── Impl/<Module>.lean         # types, sig abbrevs, reference impls (with markers)
    ├── Spec/<Module>.lean         # frozen specs plus RepoImpl-dependent spec helpers
    ├── Bundle.lean                # structure <Project>Bundle — one field per API
    ├── Harness.lean               # structure RepoImpl + canonical + joint_unsat macro
    └── Test.lean                  # #guard conformance tests against Bank.* directly
```

Multi-package benchmarks add sibling `<OtherPackage>/` dirs, each with
their own `Impl/`, `Spec/`, `Bundle.lean`. `Harness.lean` stays as a
benchmark-level singleton.

---

## The `!benchmark` marker system

Every LLM-editable slot is wrapped in a `-- !benchmark @start <key> …`
/ `-- !benchmark @end <key> …` pair. The `@end` must repeat the same
`key` and `def=<name>`.

### Active key set (7)

| Key | Wraps | `def=` | Extra fields on `@start` |
|---|---|:---:|---|
| `imports` | file-level import extension slot | — | — |
| `global_aux` | file-level helper-def slot | — | — |
| `code` | function body (reference impl in curated source; `sorry` only after pre-agent materialization) | yes | — |
| `code_aux` | per-function helper-def slot | yes | — |
| `proof` | tactic body after `by` | yes | `kind=prove\|disprove\|unsat\|sat\|joint_unsat`, `target=<spec>` (omitted only when `kind=joint_unsat`) |
| `proof_aux` | per-theorem helper-def slot | yes | — |
| `claim` | LLM's live macro invocation in `Joint.lean` (discarded at eval) | yes | `kind=joint_unsat` |

Retired (do **not** emit): `spec`, `spec_aux`, `claim_aux`, `def_aux`,
`def_body`, `precond*`, `postcond*`.

### `!solution` prefix (new third prefix — only in `Proof/Joint.lean`)

Multi-line block that lets the LLM submit structured data (the
joint-unsat spec list). *Translate does not emit `Proof/Joint.lean`*;
the pre-agent-gen stage does. Knowledge for reference only.

### `!curation` prefix

Single-line curator-only annotations. Stripped before the benchmark is
presented to the LLM. Only in `Impl/*` after curation. Forms:

```
-- !curation @review v<N> [<x| >] <name> — <loc>, <kind>, <notes>
-- !curation @human: <note>
-- !curation @question <target>: <q>
-- !curation @answer: <a>
-- !curation @v<N> [...] <name> — <notes> [RESOLVED|NOTED|ANSWERED|KEPT]
```

### Marker positioning rules (hard)

- **`imports`** — immediately after the actual `import` statements,
  BEFORE the module docstring. At file top if no imports.
- **`global_aux`** — after the module docstring, before the body.
- **`code_aux`** — file-level, immediately before its `code` slot.
- **`proof_aux`** — file-level, BEFORE the theorem or macro
  invocation. Never between `by` and the proof body.
- **`claim`** — in `Joint.lean` only; wraps the LLM's live macro
  invocation (its content is discarded at eval).

### `def=<name>` conventions

- `code` / `code_aux` — the Lean function dot-tail (`createAccount`).
- `proof` / `proof_aux` — full theorem name (`prove_<spec>`,
  `disprove_<spec>`, `unsat_<spec>`, `sat_<spec>`).
- `claim` — `joint_unsatisfiability` (there is exactly one joint slot
  per benchmark).

### Balance

Every `@start` has a matching `@end` with the same `key` and `def=`.
No nesting. Commented markers (inside `/- … -/` or `-- -- !benchmark`)
are ignored by the extractor. `def=<name>` is unique within
`(file, key)`.

---

## File templates — canonical shape

### `lakefile.toml`

```toml
name = "{Project}"
version = "0.1.0"
defaultTargets = ["{Project}"]

[[lean_lib]]
name = "{Project}"
srcDir = "."
leanOptions = [{ name = "autoImplicit", value = false }]
```

The old `[package]` form is **gone**.

### `lean-toolchain`

```
leanprover/lean4:v4.29.1
```

Override only if the upstream source forces a different version.

### Root hub `<Project>.lean`

```lean
import {Project}.Impl.<Module1>
import {Project}.Impl.<Module2>
...
import {Project}.Bundle
import {Project}.Harness
import {Project}.Spec.<Module1>
import {Project}.Spec.<Module2>
...
import {Project}.Test
```

**Do not** import any `Proof/` directory — that's a downstream artifact.

### `Impl/<Module>.lean` template

```lean
import {Project}.Impl.<DepModule>

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# {Project}.Impl.<Module>

<One-paragraph description.>

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
Implement only the function bodies.
-/

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- ── Types (no markers — fixed vocabulary) ─────────────
...

namespace Bank

-- ── API signatures (no markers — fixed vocabulary) ────
abbrev CreateAccountSig := AccountId → Ledger → Ledger
...

end Bank

-- ── Reference implementations (LLM task slots) ──────────

-- !benchmark @start code_aux def=createAccount
-- !benchmark @end code_aux def=createAccount

-- !curation @review v1 [ ] createAccount — Impl/<Module>, code, reference impl
def Bank.createAccount : Bank.CreateAccountSig :=
-- !benchmark @start code def=createAccount
  fun id ledger =>
    if ledger.any (fun a => a.id == id) then ledger
    else ⟨id, 0⟩ :: ledger
-- !benchmark @end code def=createAccount
```

The body inside the `code` marker is the curator's **reference
implementation** — real working code, not `sorry`. Pre-agent-gen
replaces it with `sorry` when emitting the LLM-facing benchmark. See
Non-Negotiables below.

```lean
```

Types live in the foundation Impl file (the one every other Impl
imports — typically `Impl/Account.lean` for the root-most types).
There is no central `Sig.lean` or `Types.lean`.

### `Spec/<Module>.lean` template (frozen, no markers)

```lean
import {Project}.Harness

/-!
# {Project}.Spec.<Module>

Specifications for <subsystem>. Each `spec_*` is a property over an
arbitrary `impl : RepoImpl`. Spec helpers that mention `RepoImpl` also
live here, before the specs.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- <natural-language description> -/
def spec_<name> (impl : RepoImpl) : Prop :=
  ∀ …, impl.<pkg>.<fn> … = …
```

Specs access API functions via `impl.<pkg>.<fn>` where `<pkg>` is the
field name in `RepoImpl` (e.g. `impl.bankLedger.createAccount`). No
markers at all — the Spec layer is entirely frozen.

### `Bundle.lean` template

```lean
import {Project}.Impl.<Module1>
import {Project}.Impl.<Module2>
...

/-!
# {Project}.Bundle

Per-package implementation bundle for the `{Project}` root package.
Collects all API signatures into one structure.

DO NOT MODIFY — benchmark infrastructure.
-/

structure {Project}Bundle where
  createAccount : Bank.CreateAccountSig
  closeAccount  : Bank.CloseAccountSig
  ...
```

Bundle struct name is `<Project>Bundle` (PascalCase). One field per
API sig, field name matches the API's Lean name (camelCase).

### `Harness.lean` template

```lean
import {Project}.Bundle

/-!
# {Project}.Harness

Benchmark harness: `RepoImpl` structure (one field per package),
`canonical` instance wiring, and the `joint_unsat` macro.

DO NOT MODIFY — benchmark infrastructure.
-/

structure RepoImpl where
  {pkg} : {Project}Bundle

def canonical : RepoImpl where
  {pkg} := {
    createAccount := Bank.createAccount
    closeAccount  := Bank.closeAccount
    ...
  }

/-- `joint_unsat spec_A spec_B [spec_C …] by <proof>` generates the
    ∧-conjunction unsat theorem. Variadic; no sort / no dedup — anti-cheat
    is enforced at `!solution` extraction during evaluation. -/
syntax "joint_unsat" ident ident ident* "by" tacticSeq : command

open Lean in
macro_rules
  | `(joint_unsat $s1 $s2 $[$rest]* by $proof) => do
    let specs := #[s1, s2] ++ rest
    let name := specs.foldl (init := `joint_unsat) fun acc s => Name.append acc s.getId
    let mut body ← `($(specs[0]!) impl)
    for s in specs[1:] do
      body ← `($body ∧ $s impl)
    `(theorem $(mkIdent name) : ¬ ∃ impl : RepoImpl, $body := by $proof)
```

For single-package benchmarks (typical), `RepoImpl` has exactly one
field named `lowerCamelCase(<Project>)`. For multi-package benchmarks
it has one field per package.

**No other macros.** The retired `solo_unsat` / `sat_witness` macros
are gone; per-module proof obligations materialize as plain theorem
statements downstream.

### `Test.lean` template

```lean
import {Project}.Impl.<Module1>
...

/-!
# {Project}.Test

`#guard` conformance tests. Guards run against `Bank.*` directly —
the curator's reference implementations live INSIDE the `code` markers
in `Impl/*.lean`. Before the LLM sees the benchmark, pre-agent-gen
replaces marker content with `sorry`; these guards catch regressions
in the reference impls themselves, not in LLM submissions.

DO NOT MODIFY — infrastructure.
-/

open Bank

#guard accountExists 1 [] == false
#guard getBalance 1 (createAccount 1 []) == some 0
#guard (transfer 1 2 30 [⟨1, 100⟩, ⟨2, 50⟩]).map totalAssets == some 150
...
```

No markers in `Test.lean`. No `Bank.Ref` namespace — that's been
retired (2026-04-20). The reference implementation is whatever the
curator wrote inside each `code` marker.

---

## `manifest.json` (derived from the tree)

At the end of translate, emit / update the manifest per the shape in
`reference/BankLedger/manifest.json` (full schema:
`docs/pipeline-schema.md`). Top-level:

```json
{
  "benchmark_id": "...",
  "description": null,
  "lean_version": "4.29.1",
  "modes_supported": ["proof", "codeproof"],
  "source": { "kind": "translated", "language": "...", "repo_url": "...", "commit_hash": "...", "path": "..." },
  "curation": { "date": "..." },
  "root_package": "{Project}",
  "files": {
    "root_hub": "{Project}.lean",
    "harness": "{Project}/Harness.lean",
    "test":    "{Project}/Test.lean",
    "lakefile": "lakefile.toml"
  },
  "packages": [
    {
      "name": "{Project}",
      "bundle": "{Project}/Bundle.lean",
      "bundle_type": "{Project}Bundle",
      "repo_impl_field": "{lowerCamelCase}",
      "modules": [
        {
          "name": "<Module>",
          "impl": "{Project}/Impl/<Module>.lean",
          "spec": "{Project}/Spec/<Module>.lean",
          "apis": [
            { "name": "createAccount", "sig": "CreateAccountSig", "type": "AccountId → Ledger → Ledger" }
          ],
          "specs": ["spec_create_zero_balance", "..."]
        }
      ]
    }
  ]
}
```

`apis[].type` is the body of the `abbrev <Sig> := <type>` in the Impl
file (exact text, including spaces around `→`). `specs[]` are the spec
names found in `Spec/<Module>.lean`.

---

## Workflow (plan-driven, one file per Write, build per file)

**`plan.json` is the contract.** Translate walks
`plan.packages[].modules[]` and emits exactly the files the plan
names, one at a time. Do NOT improvise a module that isn't in the
plan, and do NOT skip one that is. Do NOT write multiple Lean files
before running `lake build`.

**Non-negotiable write discipline.**
- One `Write` per file. Never batch-emit several `.lean` files in a
  single turn.
- After each `Write`, run `cd <project> && lake build` and wait for
  it to succeed before moving to the next file.
- If a file is larger than ~150 lines of body (e.g. an `Impl/` module
  with 8+ APIs), split its emission into: (a) Write skeleton with
  types + sig abbrevs + marker-wrapped API definitions,
  `lake build`, (b) Edit to fill each API's reference impl one at a
  time. This keeps the file buildable after every step.
- Announce each Write in one sentence: "Writing `Impl/Merkle.lean` —
  3 types, 5 APIs, 12 code slots." Then perform the Write. Then
  announce the build outcome.

### Phase 1 — Scaffolding (one Write each)

`lakefile.toml`, `lean-toolchain`, empty root hub, empty
`manifest.json`. Build the empty scaffold. That's four Writes and
one `lake build`.

### Phase 2 — Impl modules (iterate plan.packages[].modules[])

For each module `M` in `plan.json`, in dependency order (foundation
module first):

  1. Look up the four per-module lists in plan.json:
     - `M.types` — fully-defined types, emit without markers
     - `M.spec_helpers` — **curator-given vocabulary for specs**; emit
       each as a fully-defined `def` / `inductive` / `predicate`
       using `lean_form` verbatim. **No markers**, not in Bundle.
       Helpers that mention `RepoImpl` or `impl.<pkg>` must live in
       `Spec/<Module>.lean` before the specs; pure helpers live in
       `Impl/<Module>.lean`.
     - `M.api_helpers` (optional, usually empty) — fully-defined
       helpers the curator wants to hand to the LLM. No markers, not
       in Bundle.
     - `M.apis` — sig abbrevs + reference implementation defs, **each wrapped in
       `!benchmark code` / `code_aux` markers**, field contributed to
       Bundle.
  2. Write `<Project>/Impl/<M.name>.lean` in this order, top to
     bottom:
     ```
     imports
     `-- !benchmark @start imports`  … `-- !benchmark @end imports`
     docstring
     types (no markers)
     pure spec helpers (no markers)
     api helpers (no markers, if any)
     namespace Bank
       API sig abbrevs (no markers)
     end Bank
     `-- !benchmark @start global_aux` … `-- !benchmark @end global_aux`
     one `code_aux` + `code` marker pair per API (with reference impl
     body inside each `code` marker)
     ```
  3. `lake build`. Fix errors before proceeding.
  4. Announce: "Module `<M.name>` built. T types, H spec helpers,
     N API slots emitted. Moving on to `<next>`."

No module is emitted before its dependencies build clean.

### Phase 3 — Bundle + Harness (two Writes, one build)

Write `<Project>/Bundle.lean` with one field per entry in
`plan.packages[].modules[].apis[]` **only** — spec helpers and API
helpers must NOT appear as Bundle fields. Write
`<Project>/Harness.lean` with `structure RepoImpl` + `canonical`
wiring, again using only API names. `lake build`.

Verify `canonical` has exactly one field per API in the plan and no
extra fields — grep for each `<api_lean_name>` in `Harness.lean`
before calling Phase 3 complete. Count fields: it must equal
`len(plan.packages[].modules[].apis[])` summed across modules.

### Phase 4 — Spec modules (iterate plan.packages[].modules[])

For each module `M` in plan order, write
`<Project>/Spec/<M.name>.lean` when `M.specs` is non-empty or
`M.spec_helpers` contains any helper mentioning `RepoImpl` / `impl.<pkg>`.
Emit the RepoImpl-dependent helpers first, then every spec from `M.specs`
as a `def spec_<name> (impl : RepoImpl) : Prop := …`. One Write per
module, build after each one. The plan's `spec.lean_form` field is the
authoritative body — paste it under the `def` header verbatim, adjusting
only for obvious typos.

**Spec count gate.** After each Spec file, count its
`^def spec_` lines (`grep -c ...`) and confirm it matches
`plan.json[package].modules[M].specs.length`. If the plan says 11
specs and you emitted 6, stop and emit the remaining 5 — do not
proceed to the next module.

### Phase 5 — Test (one Write, one build)

Write `<Project>/Test.lean` with `#guard` tests from
`plan.test_cases[]`. One Write. Build.

### Phase 6 — Manifest + root hub (two Writes, final build)

Regenerate `manifest.json` from what was actually emitted (don't
trust the scaffold — the module list must reflect the real tree).
Update the root hub to import every emitted file except `Proof/`.
Final `lake build` must pass cleanly without `sorry` warnings in
curated `Impl/` `code` markers. `sorry` is introduced later by
pre-agent materialization, not by translate.

### If interrupted

Every phase leaves the tree in a lake-buildable state. To resume:
rerun translate and the skill should detect existing files (via a
quick `ls <project>/Impl/`) and skip already-emitted modules. Never
overwrite a file that already contains `!benchmark` markers without
confirming the curator wants it regenerated.

---

## Non-negotiables

1. **No `Sig.lean`, no `Types.lean`** — types and sigs live with the
   Impl file they describe.
2. **Spec/ has no markers** — entirely frozen.
3. **No `Proof/` emitted** — that is downstream.
4. **Fill reference impls inside `code` markers — NOT `sorry`.** The
   curator writes the actual working implementation there; pre-agent-gen
   replaces marker content with `sorry` before the LLM sees the
   benchmark. `Test.lean` `#guard`s therefore hit real code at
   curation / build time, catching regressions in the reference itself.
5. **No `Bank.Ref` namespace.** Retired 2026-04-20 in favor of the
   single-source-of-truth model above. `#guard` tests use `Bank.*`
   directly.
6. **Only 7 `!benchmark` keys** — retired keys are errors (see
   `src/vero/curation/marker.py` RETIRED_KEYS for the list).
7. **Marker positioning rules** — `imports` after actual imports,
   `proof_aux` before theorem, no nesting.
8. **Bundle + structure RepoImpl uniformly** — single-package
   benchmarks use the same shape (one field) as multi-package (more
   fields).
7. **Specs access APIs via `impl.<pkg>.<fn>`** — never bare `impl.<fn>`
   (the structure is one-level-nested, not an abbrev).
8. **Manifest items are source-backed** — translated APIs, helpers, specs,
   and reference implementations must correspond to concrete upstream
   declarations; do not invent placeholders to fill gaps.
9. **Imports use one canonical generated root** — import generated modules
   through the manifest package paths only, so the same declarations cannot
   be loaded through alternate roots.
10. **`lake build` must pass** before calling translate complete.

---

## Validation

After completing translate, the pipeline runs the validate stage
(rule-based checks in `src/vero/curation/validation/`). If the
translate output diverges from the paradigm, validate blocks the
pipeline with actionable errors. Fix and re-run translate.
