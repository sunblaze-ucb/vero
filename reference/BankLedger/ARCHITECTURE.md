# BankLedger — Architecture

Reference Lean 4 benchmark exemplifying the `RepoImpl` bundle paradigm.
Hand-crafted (no upstream source). Serves as the shape the curation
pipeline should mirror, plus two sidecar illustrations of what the
downstream pre-agent-gen stage materializes per evaluation mode.

## Pipeline Staging

`Proof/` is NOT shipped as part of the curated benchmark. It is
generated deterministically in a later stage from the `Spec/` files
plus a mode selection:

1. **Curation stage** produces the *active* library: `Impl/`, `Spec/`,
   `Harness.lean`, `Test.lean`, root hub, `lakefile.toml`.
2. **Pre-agent-gen stage** consumes the curation output + mode choice
   and emits a `Proof/<Module>.lean` per `Spec/<Module>.lean`, plus a
   `Proof/Joint.lean` when mode = `codeproof`.
3. **Agent generation** fills marker bodies in the pre-generated repo.

The illustrations in this repo (`Proof_modeproof/`,
`Proof_modecodeproof/`) show what stage 2 emits for each mode.

## Module Dependency Graph

```
Impl/Account         (types + account sigs + stubs — foundation, no imports)
    │
    ├─► Impl/Transaction   (txn sigs + stubs)
    │       │
    │       └─► Impl/Transfer  (transfer sig + stub)
    │
    ├─► Impl/Ledger        (ledger-wide sigs + stubs)
    │
    ├─► Bundle             (structure BankLedgerBundle — one field per API sig)
    │       │
    │       └─► Harness    (structure RepoImpl + canonical + joint_unsat macro)
            │
            ├─► Spec/*             (def spec_* only; parameterized by impl)
            │       │
            │       └─► Test       (#guard conformance tests against Bank.* directly)
            │
            ├─► Proof_modeproof/*       (illustration — not imported by root)
            │
            └─► Proof_modecodeproof/*   (illustration — not imported by root)
```

`BankLedger.lean` (root hub) imports the active-library files only.
The illustration sidecars live alongside but are not part of the build
— they typecheck in LSP when opened.

## File Summary

### Active library (imported by root hub)

| File | Lines | sorry (code) | Notes |
|---|---:|---:|---|
| `BankLedger.lean` | 27 | 0 | root import hub |
| `BankLedger/Bundle.lean` | 30 | 0 | `BankLedgerBundle` — per-package bundle of API sig fields |
| `BankLedger/Harness.lean` | 75 | 0 | `structure RepoImpl` (one field per package) + `canonical` + `joint_unsat` macro |
| `BankLedger/Impl/Account.lean` | 76 | 4 | types + account API stubs |
| `BankLedger/Impl/Transaction.lean` | 41 | 2 | txn API stubs |
| `BankLedger/Impl/Transfer.lean` | 31 | 1 | transfer API stub |
| `BankLedger/Impl/Ledger.lean` | 51 | 3 | ledger-wide API stubs |
| `BankLedger/Spec/Account.lean` | 34 | 0 | 4 specs (frozen, marker-free) |
| `BankLedger/Spec/Transaction.lean` | 33 | 0 | 3 specs (frozen) |
| `BankLedger/Spec/Transfer.lean` | 29 | 0 | 2 specs (frozen) |
| `BankLedger/Spec/Ledger.lean` | 22 | 0 | 2 specs (frozen) |
| `BankLedger/Test.lean` | 44 | 0 | 15 `#guard` against `Bank.*` directly |
| **Active total** | **517** | **10** | **11 files** |

### Illustrations (not imported — reference only)

| File | Lines | sorry (proof) | Notes |
|---|---:|---:|---|
| `BankLedger/Proof_modeproof/Account.lean` | 94 | 8 | 4 specs × (prove + disprove) |
| `BankLedger/Proof_modeproof/Transaction.lean` | 72 | 6 | 3 specs × 2 |
| `BankLedger/Proof_modeproof/Transfer.lean` | 54 | 4 | 2 specs × 2 |
| `BankLedger/Proof_modeproof/Ledger.lean` | 54 | 4 | 2 specs × 2 |
| `BankLedger/Proof_modecodeproof/Account.lean` | 131 | 12 | 4 specs × (prove + unsat + sat) |
| `BankLedger/Proof_modecodeproof/Transaction.lean` | 96 | 9 | 3 specs × 3 |
| `BankLedger/Proof_modecodeproof/Transfer.lean` | 70 | 6 | 2 specs × 3 |
| `BankLedger/Proof_modecodeproof/Ledger.lean` | 70 | 6 | 2 specs × 3 |
| `BankLedger/Proof_modecodeproof/Joint.lean` | 91 | 0 | 1 joint-unsat slot (dormant, all-commented pre-seed) |
| **Illustration total** | **732** | **55** | **9 files** |

**Grand total:** 20 files, 1249 lines.

## API Layer (`Impl/`)

### `Impl/Account.lean`

Types (fully defined, no markers): `AccountId`, `Balance`, `Account`, `Ledger`.

| Fn | Signature abbrev | Kind |
|---|---|---|
| `Bank.createAccount` | `AccountId → Ledger → Ledger` | exec-fn (API) |
| `Bank.closeAccount` | `AccountId → Ledger → Ledger` | exec-fn (API) |
| `Bank.accountExists` | `AccountId → Ledger → Bool` | exec-fn (API) |
| `Bank.getBalance` | `AccountId → Ledger → Option Balance` | exec-fn (API) |

### `Impl/Transaction.lean`

| Fn | Signature abbrev | Kind |
|---|---|---|
| `Bank.deposit` | `AccountId → Balance → Ledger → Option Ledger` | exec-fn (API) |
| `Bank.withdraw` | `AccountId → Balance → Ledger → Option Ledger` | exec-fn (API) |

### `Impl/Transfer.lean`

| Fn | Signature abbrev | Kind |
|---|---|---|
| `Bank.transfer` | `AccountId → AccountId → Balance → Ledger → Option Ledger` | exec-fn (API) |

### `Impl/Ledger.lean`

| Fn | Signature abbrev | Kind |
|---|---|---|
| `Bank.totalAssets` | `Ledger → Balance` | exec-fn (API) |
| `Bank.accountList` | `Ledger → List AccountId` | exec-fn (API) |
| `Bank.numAccounts` | `Ledger → Nat` | exec-fn (API) |

10 API stubs total (the `code` benchmark tasks).

## Four categories of curated items

Every curated item falls into one of four categories (plus supporting roles `type` / `test`):

| Category | What it becomes | Bundle field? | Markers? |
|---|---|---|---|
| **API** | sig abbrev + stub with reference impl inside `!benchmark code` marker → LLM's implementation obligation | yes | yes |
| **API helper** | (usually absent — LLM invents its own in `code_aux`). If curator opts in: fully-defined `def` in `Impl/` | no | no |
| **Spec** | `def spec_<name> (impl : RepoImpl) : Prop := …` in `Spec/<Module>.lean` → proof obligation downstream | no | no (Spec layer is frozen) |
| **Spec helper** | Fully-defined function or predicate in `Impl/` (or framework file) that specs reference by bare name | no | no |

BankLedger itself exercises only **API** and **Spec** — the model is simple enough that no spec helpers are needed. Real-world translations (e.g. `benchmarks/deposit_sc/`) commonly need `Spec helper` items: predicates like `Valid`, `isMerkle`, `isCompleteTree` and vocabulary like `leavesIn`, `height`, `nodesIn` are fully-defined in `Impl/` and referenced by bare name in `Spec/` bodies.

## Bundle (`BankLedger/Bundle.lean`)

`structure BankLedgerBundle where` — the root package's bundle. **One field per API** (category=api), and only those. Spec helpers and API helpers do NOT appear as Bundle fields. BankLedger has 10 APIs = 10 fields. Per-package bundles live in `<Package>/Bundle.lean`. Single-package benchmarks have one Bundle; multi-package benchmarks have one per sibling.

## Harness (`Harness.lean`)

- `structure RepoImpl where` — one field per package, each typed as `<PackageName>Bundle`. Single-package BankLedger: `bankLedger : BankLedgerBundle`. Multi-package would add more fields of the same shape.
- `canonical : RepoImpl` — wires each package's bundle fields to the `Bank.*` stubs from `Impl/`. Access: `canonical.bankLedger.createAccount` etc.
- `joint_unsat` macro — variadic, produces the ∧-conjunction unsat theorem. Specs appear in the caller's order (no sort, no dedup — anti-cheat is enforced at `!solution` extraction during evaluation).

No other macros. Per-module proof stubs are plain theorem statements in the illustration files; they do not consume macros.

**Spec access pattern.** Specs access **API** functions via `impl.<pkg>.<fn>` (e.g. `impl.bankLedger.createAccount`) — that's how the framework keeps the spec body agnostic to the specific implementation. Specs access **Spec helpers** (curator-given vocabulary) by bare name. The rule: if the identifier appears under `impl.<pkg>.<…>`, it's an API (in the Bundle, stubbed); if it's bare, it's a spec helper (fully defined in `Impl/`, not in the Bundle). A bare reference that isn't a spec helper is a plan-stage error.

## Spec Layer (`Spec/`)

Each file holds `def spec_* (impl : RepoImpl) : Prop := …`. No theorems. 11 specs total:

| File | Specs |
|---|---|
| `Spec/Account.lean` | `spec_create_zero_balance`, `spec_create_exists`, `spec_close_removes`, `spec_close_preserves_others` |
| `Spec/Transaction.lean` | `spec_deposit_increases`, `spec_withdraw_decreases`, `spec_withdraw_insufficient` |
| `Spec/Transfer.lean` | `spec_transfer_preserves_total`, `spec_transfer_updates_both` |
| `Spec/Ledger.lean` | `spec_total_create_invariant`, `spec_num_matches_list` |

## Illustration Layers

### `Proof_modeproof/` — proof mode

Per `Spec/<Module>.lean`, one mirror file with two theorem stubs per spec:

- `theorem prove_S    : spec_S canonical := by sorry` (`kind=prove target=spec_S`)
- `theorem disprove_S : ¬ spec_S canonical := by sorry` (`kind=disprove target=spec_S`)

Each with paired `proof_aux`. File-level `imports` + `global_aux` at top. LLM fills exactly one of the pair per spec.

**22 stubs total** (11 specs × 2). No `Joint.lean`, no macros consumed.

### `Proof_modecodeproof/` — codeproof mode

Per `Spec/<Module>.lean`, one mirror file with three direct theorem stubs per spec:

- `theorem prove_S : spec_S canonical := by sorry`                         (`kind=prove`)
- `theorem unsat_S : ¬ ∃ impl : RepoImpl, spec_S impl := by sorry`         (`kind=unsat`)
- `theorem sat_S   : ∃ impl : RepoImpl, spec_S impl := by sorry`           (`kind=sat`)

**33 stubs total** (11 specs × 3). LLM fills exactly one body per spec; the `sat_S` case must be paired with S listed in the `!solution` block in `Joint.lean`.

`Joint.lean` contains exactly ONE pre-seeded joint-unsat slot. Pre-seed has all LLM-editable content *commented out* — the slot is dormant until the LLM chooses to claim it. Layout:

```
-- !benchmark @start imports
-- !benchmark @end imports

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- !solution @start def=joint_unsatisfiability kind=joint_unsat
-- specs=[<FILL: comma-separated spec names, e.g. spec_a, spec_b>]
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

`imports` and `global_aux` are file-level extension slots — LLM may add
imports and helper defs to the file. Present on every editable file
(Impl, per-module Proof illustrations, and Joint.lean).

At evaluation: the `!solution` `specs=[…]` list is the source of truth (evaluator rejects duplicates); the `proof` body is spliced; the `joint_unsat` macro is rerendered from those two inputs. The LLM's own `claim` content is discarded.

## Mode Coverage

Per spec S, exactly one must be `sorry`-free in the LLM's submission:

| Mode | Valid coverage |
|---|---|
| `proof` — canonical given | `prove_S` ⊻ `disprove_S` |
| `codeproof` — LLM writes `Bank.*` | `prove_S`, OR `unsat_S`, OR (`sat_S` AND S named in the proved `!solution` in `Joint.lean`) |

Logical consistency (codeproof): the three buckets are mutually exclusive on any consistent submission.

## Test Layer (`Test.lean`)

15 `#guard` conformance tests call `Bank.*` directly. The curator's reference implementations live inside each API's `code` marker in `Impl/*.lean` — pre-agent-gen replaces marker content with `sorry` before the LLM sees the benchmark, so these guards catch regressions in the reference itself at curation / build time. No separate `Bank.Ref` namespace (retired 2026-04-20).

## Namespace Plan

| File | Namespace | Notes |
|---|---|---|
| `Impl/*.lean` | `Bank` (for sigs) + `Bank.<name>` (for defs) | `namespace Bank` wraps sig abbrevs; def uses dot-prefix. |
| `Harness.lean` | top-level | `RepoImpl`, `canonical`, `joint_unsat` macro. |
| `Spec/*.lean` | top-level | `def spec_*` visible after `import Harness`. |
| `Proof_modeproof/*.lean`, `Proof_modecodeproof/*.lean` | top-level | theorems reference `spec_*` and `canonical` unqualified. |
| `Test.lean` | top-level + `open Bank` for unqualified `#guard` access |

## Marker Inventory

Three reserved prefixes:

- **`!benchmark`** — multi-line `@start`/`@end` task regions. Evaluator extracts bodies and splices into the pristine template.
- **`!solution`** — multi-line `@start`/`@end` LLM-supplied structured data (e.g. joint-unsat spec list). Extracted separately from `!benchmark` and used to rerender task content.
- **`!curation`** — single-line curator-facing annotations. Stripped before the benchmark is presented to the LLM and before evaluation. Present only in `Impl/*` in the active library.

### `!benchmark` task markers

| Key | Typical `def=` | Extra fields on `@start` | Where |
|---|---|---|---|
| `imports` | — | — | Every editable file. **Position: immediately after the actual `import` statements, BEFORE the module docstring.** (At file top if there are no imports.) |
| `global_aux` | — | — | Every editable file. Positioned after the docstring, before the body. |
| `code` | fn name (e.g. `createAccount`) | — | `Impl/*` |
| `code_aux` | fn name | — | `Impl/*` (paired with `code`) |
| `proof` | theorem name | `kind=prove\|disprove\|unsat\|sat\|joint_unsat`, `target=spec_X` (omitted for `joint_unsat` — specs come from `!solution`) | Per-module Proof illustrations + `Joint.lean` |
| `proof_aux` | theorem name | — | Per-module + `Joint.lean`. File-level position — in `Joint.lean` it sits BEFORE `claim` so helpers land outside the theorem. |
| `claim` | claim name (e.g. `joint_unsatisfiability`) | `kind=joint_unsat` | `Joint.lean` only. No paired `*_aux` — helpers go in `proof_aux` or `global_aux`. |

`@end` requires only `key` + `def`.

### `!solution` markers

| Kind | Body fields |
|---|---|
| `joint_unsat` | `specs=[<comma-separated spec names>]` using `[]` notation |

### `!curation` annotations

Single-line, comment-anchored, curator-only. Forms:

| Kind | Form |
|---|---|
| `@review v<N>` | `-- !curation @review v<N> [<x\| >] <name> — <loc>, <kind>, <notes>` |
| `@v<N>` (archived) | `-- !curation @v<N> [...] <name> — <notes> [RESOLVED\|NOTED\|ANSWERED\|KEPT]` |
| `@human:` | `-- !curation @human: <note>` |
| `@question` | `-- !curation @question <target>: <q>` |
| `@answer:` | `-- !curation @answer: <a>` |

## Key Design Decisions

1. **No central `Sig.lean` or `Types.lean`.** Signatures live in the `Impl/*.lean` file that owns them; types live in `Impl/Account.lean` (the foundation). Minimizes indirection.

2. **`Spec/` holds only `def spec_*`; no theorems; no markers.** Separates WHAT (the property) from HOW (the direction of proof). Spec layer is entirely frozen.

3. **Specs parameterized by `impl : RepoImpl`.** Allows theorem stubs for any impl, not just `canonical`. Enables `∃ impl, spec_S impl` (sat) and `¬ ∃ impl, spec_S impl` (unsat / joint-unsat) without committing to a specific impl.

4. **Proof layer is downstream of curation.** Per-module proof files and `Joint.lean` are materialized per-mode at pre-agent-gen. Curation output ships Impl/Spec/Harness/Test only.

5. **Per-module proof stubs use direct theorems (no macros).** `prove_S` / `disprove_S` / `unsat_S` / `sat_S` are plain theorem statements with `:= by sorry` bodies. Only the joint-unsat claim uses the `joint_unsat` macro (because its statement has variadic arity).

6. **`joint_unsat` is minimal.** No sorting, no deduplication. Anti-cheat for joint-unsat claims is enforced at `!solution` extraction: the evaluator reads `specs=[…]`, rejects duplicates, and rerenders the macro invocation + body from that list. The LLM's own `claim` content (their locally-compiled macro call) is discarded at evaluation.

7. **No `claim_aux`.** The `claim` marker wraps scratch content that eval discards; its only purpose is local compilation. Helper defs for the proof go in `proof_aux` (file-level, before `claim`) or `global_aux` — there is no per-claim aux slot.

8. **One joint slot per benchmark, regardless of package count.** `Joint.lean` is a top-level singleton; specs from any package appear in a single `!solution` list (fully qualified if namespaced per package).

9. **Reference implementation lives inside `code` markers, not in a `Bank.Ref` namespace** (retired 2026-04-20). The curator writes real working code inside each `code` marker in `Impl/*.lean`; pre-agent-gen replaces marker content with `sorry` before the LLM sees the benchmark. `Test.lean` `#guard`s hit `Bank.*` directly. One source of truth; no duplicate reference.
