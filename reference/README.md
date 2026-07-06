# Reference Benchmarks

Hand-curated Lean 4 projects that serve as the canonical shape the
curation pipeline should produce. The curation skills (`vero-translate`,
`vero-plan`, `vero-source-*`) will cite this directory as the exemplar.

**Contents:**

| Path | Purpose |
|---|---|
| `BankLedger/` | The reference benchmark. Active curation-stage library plus two sidecar illustrations of the pre-agent-gen output (one per evaluation mode). |
| `BankLedger-solution/` | Solved copy (legacy — awaiting mirror from current `BankLedger/`). |

## Pipeline Staging

`Proof/` is **not** a curation-stage artifact. The pipeline has three
stages, and the reference repo only ships stage 1:

1. **Curation stage** produces `Impl/`, `Spec/`, `Harness.lean`,
   `Test.lean`, root hub, `lakefile.toml`, `manifest.json`. Authoritative
   and shared across evaluation modes.
2. **Pre-agent-gen stage** is mechanical and deterministic: it consumes
   the curation output + a mode selection and emits
   `Proof/<Module>.lean` per `Spec/<Module>.lean` (plus
   `Proof/Joint.lean` if mode = `codeproof`).
3. **Agent generation** fills marker bodies in the pre-generated repo.

`BankLedger/BankLedger/Proof_modeproof/` and
`BankLedger/BankLedger/Proof_modecodeproof/` are **illustrations** of
stage 2 output for the two modes. They are not imported by the root
hub — they live alongside as reference for what the pipeline will
produce.

## The `BankLedger` Paradigm

```
Active library (root hub imports):
  Impl/           — types, signatures, function stubs (:= sorry)
  Harness.lean    — RepoImpl bundle, canonical instance, joint_unsat macro
  Spec/           — def spec_* only (properties over any impl)
  Test.lean       — #guard conformance tests against Bank.* directly

Illustrations (not imported):
  Proof_modeproof/        — per-module (prove_S + disprove_S) stubs
  Proof_modecodeproof/    — per-module (prove_S + unsat_S + sat_S) stubs
                            + Joint.lean (one joint-unsat slot, dormant pre-seed)
```

See `BankLedger/ARCHITECTURE.md` for the full module graph, per-file
table, marker inventory, and design decisions.

### Active Library

#### `Impl/`

Each module file owns: the types it introduces, the signatures of its
API as `abbrev Bank.<Name>Sig` inside `namespace Bank`, and the function
stubs as `def Bank.<name> : Bank.<Name>Sig := sorry` wrapped in `code` /
`code_aux` markers.

Types and sigs are frozen (no markers). Only the function bodies are
the LLM's task in `codeproof` mode. In `proof` mode, the bodies are
given (reference impl).

There is no central `Sig.lean` or `Types.lean` — each file stands on
its own.

#### `Bundle.lean` + `Harness.lean`

Uniform bundle paradigm:

1. **`<Package>/Bundle.lean`** per package — declares
   `structure <PackageName>Bundle where` with one field per API
   signature. For BankLedger: `BankLedgerBundle` with 10 fields.
2. **`Harness.lean`** — declares `structure RepoImpl where` with one
   field per package (each typed as `<PackageName>Bundle`).
   Single-package BankLedger: `bankLedger : BankLedgerBundle`.
   Multi-package adds more fields of the same shape.
3. **`canonical : RepoImpl`** wires each package's bundle fields to the
   `Bank.*` stubs from `Impl/`. In `proof` mode `canonical` is the
   reference impl; in `codeproof` mode it points at LLM-filled stubs.
4. **`joint_unsat spec_A spec_B [spec_C …] by <proof>`** macro —
   generates
   `theorem joint_unsat.spec_A.spec_B.… : ¬ ∃ impl : RepoImpl, spec_A impl ∧ … := by <proof>`.
   No sorting, no deduplication: the caller's order is preserved.
   Anti-cheat for joint-unsat claims is enforced at evaluation by
   extracting the spec list from the companion `!solution` marker (see
   below) and rerendering the macro from the extracted list.

Only one macro exists — per-module proof stubs use plain theorem
statements, not macros. Specs access APIs via `impl.<pkg>.<fn>`
(e.g. `impl.bankLedger.createAccount`).

#### `Spec/`

One file per Impl module. Each file holds only
`def spec_* (impl : RepoImpl) : Prop := …`, no theorems. The Spec
layer is **entirely frozen** — no `!benchmark` markers, no LLM-editable
regions. Specs are parameterized by an arbitrary `impl` so they can
quantify over all impls (for `unsat_S` / joint-unsat) or be applied to
`canonical` (for `prove_S` / `disprove_S`).

#### `Test.lean`

15 `#guard` conformance tests call `Bank.*` directly. The curator's
reference implementations live inside each API's `code` marker in
`Impl/*.lean`; pre-agent-gen replaces marker content with `sorry`
before the LLM sees the benchmark, so these guards catch regressions
in the reference itself at curation / build time. There is no
separate `Bank.Ref` namespace (retired 2026-04-20) — one source of
truth.

### Illustrations

#### `Proof_modeproof/` — proof mode

Per spec S, two theorem stubs:

- `theorem prove_S    : spec_S canonical := by sorry` (`kind=prove target=spec_S`)
- `theorem disprove_S : ¬ spec_S canonical := by sorry` (`kind=disprove target=spec_S`)

Each with paired `proof_aux`. File-level `imports` + `global_aux` at top.
LLM fills exactly one of the pair per spec; the other stays `sorry`.

No `Joint.lean`, no anti-cheat macros consumed — `canonical` is given
and the LLM only proves over it.

#### `Proof_modecodeproof/` — codeproof mode

Per spec S, three direct theorem stubs (no macros):

| Kind | Theorem | Marker kind |
|---|---|---|
| prove | `prove_S : spec_S canonical` | `kind=prove` |
| unsat | `unsat_S : ¬ ∃ impl : RepoImpl, spec_S impl` | `kind=unsat` |
| sat | `sat_S : ∃ impl : RepoImpl, spec_S impl` | `kind=sat` |

Each with paired `proof_aux`. LLM fills exactly one body per spec; the
other two stay `sorry`. The `sat_S` case is paired with S listed in the
`!solution` block in `Joint.lean`.

`Joint.lean` contains exactly ONE pre-seeded joint-unsat slot,
named `joint_unsatisfiability`. All LLM-editable content is
COMMENTED OUT in the pre-seed — the slot is dormant until the LLM
chooses to claim it. Structure:

```
-- !benchmark @start imports
-- !benchmark @end imports

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- !solution @start def=joint_unsatisfiability kind=joint_unsat
-- specs=[<FILL: comma-separated spec names>]
-- !solution @end def=joint_unsatisfiability kind=joint_unsat

-- !benchmark @start proof_aux def=joint_unsatisfiability
-- !benchmark @end proof_aux def=joint_unsatisfiability

-- !benchmark @start claim def=joint_unsatisfiability kind=joint_unsat
-- joint_unsat <specs> by
-- !benchmark @end claim def=joint_unsatisfiability

-- !benchmark @start proof def=joint_unsatisfiability kind=joint_unsat
-- sorry
-- !benchmark @end proof def=joint_unsatisfiability
```

Note the `proof_aux` slot sits at file level, BEFORE `claim`. That
way LLM helper defs live outside the theorem, not between `by` and
the proof body. There is no `claim_aux` — the `claim` content is
discarded at eval, so no helpers are needed for it; use `proof_aux`
or `global_aux` instead.

To claim a joint-unsat over ≥ 2 specs, the LLM:

1. Edits `!solution`: replaces the placeholder with
   `specs=[spec_A, spec_B, …]` in `[]` notation.
2. Uncomments the `claim` marker body and writes
   `joint_unsat spec_A spec_B by` in matching order (so the file
   compiles locally).
3. Uncomments the `proof` marker body and replaces `sorry` with a
   tactic proof.
4. Optionally fills `proof_aux` with helper defs.

At evaluation time:

- `!solution` `specs=[…]` is the source of truth. Duplicates rejected
  (no faked arity).
- The `!benchmark proof` body is extracted.
- The evaluator rerenders `joint_unsat <specs> by <body>` from those
  two inputs. The LLM's own `claim` content is discarded — it exists
  only so the LLM-working file compiles locally.

**Multi-package:** regardless of package count, there is exactly one
`Joint.lean` and one joint slot per benchmark. Specs from any package
appear in the same `!solution` list (fully qualified if the package
namespaces its specs).

## Mode Coverage

Per spec S in the benchmark, **exactly one** of the following claims
must be `sorry`-free in the LLM's submission:

### Mode 1 — `proof` (canonical given)

- `prove_S` (proves `spec_S canonical`) **xor** `disprove_S` (proves
  `¬ spec_S canonical`).

The LLM cannot change `canonical`, so it picks the direction that is
actually true for the given impl.

### Mode 2 — `codeproof` (LLM writes `Bank.*` implementations)

One of three mutually-exclusive buckets:

| Bucket | Claim | Evidence |
|---|---|---|
| 1 | `canonical` (LLM's impl) satisfies S | `prove_S` body non-sorry |
| 2 | S is inherently unsat | `unsat_S` body non-sorry |
| 3 | S is individually satisfiable AND conflicts jointly | `sat_S` body non-sorry AND S named in the proved `!solution` list in `Joint.lean` |

Logical exclusivity: if canonical satisfies S then S isn't inherently
unsat; if S is inherently unsat then no witness impl exists so case 3
fails; if S has a witness then solo-unsat is false. The LLM assigns
each spec to exactly one bucket at evaluation.

## Marker Convention

Three reserved prefixes, each with a distinct purpose:

- **`!benchmark`** — multi-line `@start`/`@end` task regions. Consumed
  by the evaluator at extraction / splice time.
- **`!solution`** — multi-line `@start`/`@end` LLM-supplied structured
  data (e.g. joint-unsat spec list). Extracted separately from
  `!benchmark` task regions; drives rerendering of joint-claim
  theorems at eval.
- **`!curation`** — single-line curator-facing annotations. Removed
  before the benchmark is presented to the LLM and before evaluation.
  Present only in `Impl/*`.

### `!benchmark` markers

Every benchmark task is wrapped in
`-- !benchmark @start <key> [field=value …] … -- !benchmark @end <key> def=<name>`.

| Key | Wraps | Where | Extra fields on `@start` |
|---|---|---|---|
| `imports` | File-level import extension slot — must sit immediately after the actual `import` statements (before the module docstring); at file top if the file has no imports | editable files | — |
| `global_aux` | File-level helper-def slot — positioned after the docstring, before the body | editable files | — |
| `code` | Function body (the `sorry` in `Impl/`) | `Impl/*` | `def=` |
| `code_aux` | Per-function helper-def slot | `Impl/*` | `def=` |
| `proof` | Tactic body only (the `sorry` after `by`) | Per-module Proof illustrations + `Joint.lean` | `def=`, `kind=prove\|disprove\|unsat\|sat\|joint_unsat`, `target=<spec>` (omitted for `joint_unsat` — specs come from `!solution`) |
| `proof_aux` | Helper-def slot, file-level position. In `Joint.lean` it sits BEFORE `claim` so defs land outside the theorem. | Per-module + `Joint.lean` | `def=` |
| `claim` | LLM's live macro invocation (discarded at eval). No paired `*_aux` — helpers go in `proof_aux` or `global_aux`. | `Joint.lean` only | `def=`, `kind=joint_unsat` |

`@end` requires only `key` + `def=`.

`Spec/*.lean` is **frozen** in all current modes — no benchmark
markers. Non-task content never gets markers: types, `abbrev`
signatures, `RepoImpl`, `canonical`, macro definitions, `#guard` tests.

### `!solution` markers

Multi-line `@start`/`@end` pairs. Body lines have the form
`-- <field>=<value>`. One field per line.

| Kind | Body fields |
|---|---|
| `joint_unsat` | `specs=[<comma-separated spec names>]` using `[]` notation |

The evaluator extracts the field values and uses them to rerender the
paired `!benchmark claim` / `proof` content.

### `!curation` annotations

Single-line, comment-anchored, curator-only. Form:
`-- !curation @<kind> [params] — <notes>`.

| Kind | Form |
|---|---|
| `@review v<N>` | `-- !curation @review v<N> [<x\| >] <name> — <location>, <kind>, <notes>` |
| `@v<N>` (archived) | `-- !curation @v<N> [...] <name> — <old notes> [RESOLVED\|NOTED\|ANSWERED\|KEPT]` |
| `@human:` | `-- !curation @human: <note>` |
| `@question` | `-- !curation @question <target>: <q>` |
| `@answer:` | `-- !curation @answer: <a>` |

Curation annotations never form pairs and never enclose content — they
tag a nearby definition or live standalone.

## Non-Negotiables

1. No central `Sig.lean`, no `Types.lean` — types and sigs live with
   the function they describe.
2. `Spec/` has only `def spec_*`, no theorems, and **no markers**
   (entirely frozen).
3. `Proof/` is NOT a curation-stage artifact. It is materialized
   per-mode at pre-agent-gen.
4. Per-module proof stubs use direct theorem statements (no macros).
   Only the joint-unsat claim uses the `joint_unsat` macro.
5. `#guard` conformance tests in `Test.lean` must pass on the
   reference impls.
6. LLM edits only inside `!benchmark` + `!solution` marker regions.
7. For joint-unsat claims, the `!solution` `specs=[…]` list is the
   source of truth; the LLM's `claim` body is extracted but discarded
   at evaluation (the evaluator rerenders the macro invocation from
   `!solution` + the `proof` body).

## Build

```bash
cd reference/BankLedger
lake build        # builds the active library (11 files)
```

The illustrations (`Proof_modeproof/`, `Proof_modecodeproof/`) are not
part of the build. Open them in an editor to inspect the shape
(LSP will typecheck them on demand).

Lean toolchain pinned to `leanprover/lean4:v4.29.1`.
