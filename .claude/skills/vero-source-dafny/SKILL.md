---
name: vero-source-dafny
description: Load BEFORE translating Dafny source to Lean 4. Provides Dafny-specific classification rules, type mappings, and patterns for mapping Dafny constructs (method / function / predicate / lemma / datatype / class) into the ratified bundle paradigm (Impl/ + Spec/ + Bundle + Harness). Pair with vero-discover, vero-plan, vero-translate, and vero-dafny-pitfalls.
allowed-tools: Read, Write, Edit, Bash, Grep, Glob
---

# VCG Source: Dafny → Lean 4

Dafny-specific classification and translation patterns for the
ratified curation paradigm. The **shape of the emitted Lean** is
pinned by `reference/BankLedger/` + `.claude/skills/vero-translate/SKILL.md` —
this skill teaches the *language mapping*.

## When to use

- Classifying items in a Dafny (`.dfy`) source (with `vero-discover`).
- Writing the translation plan for a Dafny source (with `vero-plan`).
- Emitting Lean from Dafny (with `vero-translate`).

## Output-shape recap (non-negotiable)

For each source-side module you translate:

- **`<Project>/Impl/<Module>.lean`** holds:
  - Types (fully defined, no markers).
  - `namespace Bank … abbrev <Fn>Sig := …` per API signature (no
    markers).
  - `def Bank.<fn> : Bank.<Fn>Sig := <translated reference impl>`
    wrapped in `code` / `code_aux` markers.
  - `!curation @review v1` annotations on each reference implementation.

- **`<Project>/Spec/<Module>.lean`** holds *only*
  `def spec_<…> (impl : RepoImpl) : Prop := …`. Frozen; no markers.
  Spec bodies access APIs via `impl.<repo_impl_field>.<fn>`.

- **`<Project>/Bundle.lean`** + `<Project>/Harness.lean` are shared
  across modules; translate emits them once per benchmark.

- **`Test.lean`** carries `#guard` conformance tests against
  `Bank.*` directly (no `Bank.Ref` namespace — retired 2026-04-20).

See `.claude/skills/vero-translate/SKILL.md` for exact file templates.

## Classification rules

For each top-level Dafny item, decide what Lean artifact it becomes.

| Dafny item | Lean artifact | Notes |
|---|---|---|
| `datatype` | `inductive` in Impl (foundation file) | No markers; fully defined. |
| `type` (alias) | `abbrev` in Impl (foundation file) | No markers. |
| `type` (opaque) | `opaque` in Impl | No markers; axiomatize via `axiom`. |
| `class` / `trait` | `structure` in Impl + API `abbrev <Fn>Sig` per method | Methods → API reference implementations (`code` markers); class invariants often → `spec_*`. |
| `method` | `def Bank.<fn> : Bank.<Sig> := <translated reference impl>` in Impl + one `spec_*` per `ensures` | `ensures` clauses translate to specs, not inline theorems. |
| `function` (non-ghost) | Same as `method` — API with sig + translated body + `ensures → spec_*`. | |
| `function` (ghost, vocabulary) | Full-body `def` in Impl or Spec helper — **no markers** | Vocabulary used by other specs (`toSeq`, `isValid`). Body given; not a benchmark task. |
| `predicate` | `Prop`-returning vocabulary def in Impl or Spec, no markers | |
| `lemma` (states a property worth tracking) | `spec_*` entry in plan.json | Lemmas become specs in the new paradigm. |
| `lemma` (proof helper only) | Drop from plan — becomes `proof_aux` downstream | — |
| `method` marked `{:axiom}` | `axiom <name> : <type>` in Impl | Documents external guarantees. |
| Test (`method Main` or `assert`) | `#guard` in `Test.lean` | Computable values only. |

**Classify by role, not keyword.** A `function` marked ghost in Dafny
that gets used by other specs is vocabulary → Spec helper, no
markers. A `method` that implements `push` is an API → `code` slot,
markers.

## Type mapping

| Dafny | Lean 4 |
|---|---|
| `int` | `Int` |
| `nat` | `Nat` |
| `bool` | `Bool` |
| `string` | `String` |
| `char` | `Char` |
| `real` | `Float` (prefer `Rat` if exact arithmetic matters) |
| `seq<T>` | `List T` |
| `seq<char>` | `String` (usually) |
| `set<T>` | `List T` with uniqueness spec, **or** `Finset T` if Mathlib is in scope |
| `multiset<T>` | `List T` (preserves multiplicity) |
| `map<K,V>` | `List (K × V)` with uniqueness spec |
| `array<T>` | `Array T` |
| `T?` (nullable) | `Option T` |
| tuple `(T, U)` | `T × U` |
| `function T -> U` | `T → U` |
| `datatype Foo = A \| B(x: Int)` | `inductive Foo where \| A \| B (x : Int)` |

Arrows in Lean are `→` (U+2192), not `->`.

## API translation pattern

Dafny:
```dafny
method CreateAccount(id: int, ledger: Ledger) returns (r: Ledger)
    requires /* … */
    ensures /* post */
{ /* impl */ }
```

plan.json entry:
```json
{
  "upstream_name": "CreateAccount",
  "lean_name": "createAccount",
  "sig_abbrev": "CreateAccountSig",
  "lean_type": "AccountId → Ledger → Ledger",
  "opaque": false,
  "nl_description": "Add a new account with the given id to the ledger."
}
```

Emitted Impl:
```lean
namespace Bank
abbrev CreateAccountSig := AccountId → Ledger → Ledger
end Bank

-- !benchmark @start code_aux def=createAccount
-- !benchmark @end code_aux def=createAccount

-- !curation @review v1 [ ] createAccount — Impl/Account, code, reference impl
def Bank.createAccount : Bank.CreateAccountSig :=
-- !benchmark @start code def=createAccount
  -- translated Dafny body, not `sorry`
  ...
-- !benchmark @end code def=createAccount
```

### Partial functions

When Dafny declares `requires`:
- **Total** (condition always discharged by types): drop the
  `requires`; Lean type captures it.
- **Partial with caller-supplied witness**: `(h : <precond>) → <return>`.
- **Partial expecting failure reporting**: `Option <return>` or
  `Except Err <return>`.

Match the project's other partial APIs for consistency.

## Spec translation pattern

### `ensures` on an API

Each `ensures` clause becomes one `spec_*` entry:

```dafny
method Deposit(id: int, amt: nat, l: Ledger) returns (r: Option<Ledger>)
    ensures r.Some? ==> Sum(r.value) == Sum(l) + amt
```

plan.json:
```json
{
  "name": "spec_deposit_preserves_sum",
  "nl_description": "After a successful deposit, the total equals the previous total plus the amount.",
  "lean_form": "∀ (id : AccountId) (amt : Balance) (l : Ledger) (l' : Ledger), impl.bankLedger.deposit id amt l = some l' → impl.bankLedger.totalAssets l' = impl.bankLedger.totalAssets l + amt",
  "apis_referenced": ["deposit", "totalAssets"],
  "curator_intended_truth": "prove"
}
```

Emitted Spec:
```lean
/-- After a successful deposit, the total equals the previous total plus the amount. -/
def spec_deposit_preserves_sum (impl : RepoImpl) : Prop :=
  ∀ (id : AccountId) (amt : Balance) (l : Ledger) (l' : Ledger),
    impl.bankLedger.deposit id amt l = some l' →
    impl.bankLedger.totalAssets l' = impl.bankLedger.totalAssets l + amt
```

### Standalone `lemma`

A lemma whose statement encodes a property the benchmark should
track:
```dafny
lemma DepositCommutes(a b: Value, l: Ledger)
    ensures Deposit(a, Deposit(b, l).value) == Deposit(b, Deposit(a, l).value)
```
→ plan.json `spec_deposit_commutes` (same schema as above).

A pure proof helper (no new property): drop from the plan.

## Class `invariant` pattern

```dafny
class Ledger {
  var accounts: seq<Account>;
  predicate Valid() { NoDuplicateIds(accounts) }
  method Deposit(id, amt) requires Valid() ensures Valid() { … }
}
```

1. `Ledger` struct in Impl foundation file (no markers).
2. `Valid` is vocabulary — Spec helper `def valid : Ledger → Prop` if
   purely spec; foundation-file helper if also used in Impl code.
3. `Deposit` → API reference implementation with `code` markers.
4. `requires Valid() + ensures Valid()` → one
   `spec_deposit_preserves_valid`.

## Common pitfalls (see `vero-dafny-pitfalls`)

- Dafny's `seq[i]` is total with side-condition `i < |seq|`; Lean
  `List.get?` returns `Option`. Choose one consistently.
- `multiset` semantics don't map cleanly — pick `List` with explicit
  multiplicity spec or document divergence.
- `assume` clauses are red flags; surface as `!curation @review` in
  the emitted Impl.

Load `vero-dafny-pitfalls` before translating any non-trivial item.

## Pair with

- `vero-plan` — consumes Dafny classifications.
- `vero-translate` — emits Lean per the templates.
- `vero-dafny-pitfalls` — Dafny→Lean corner cases.
- `vero-lean-pitfalls` — universal Lean traps.
