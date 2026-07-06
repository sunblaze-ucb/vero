---
name: vero-source-verus
description: Load BEFORE translating Verus source (Rust with verus! macro) to Lean 4. Provides Verus-specific classification rules (spec/proof/exec fn modes), type mappings (Seq/Map/Set vs List/AssocList), and patterns for mapping Verus constructs into the ratified bundle paradigm (Impl/ + Spec/ + Bundle + Harness). Pair with vero-discover, vero-plan, vero-translate, and vero-verus-pitfalls.
allowed-tools: Read, Write, Edit, Bash, Grep, Glob
---

# VCG Source: Verus → Lean 4

Verus-specific classification and translation patterns for the
ratified curation paradigm. The **shape of the emitted Lean** is
pinned by `reference/BankLedger/` + `.claude/skills/vero-translate/SKILL.md` —
this skill teaches the *language mapping*.

**Worked upstream exemplar:** `reference/BankLedger-source-verus/`
translates 1:1 into `reference/BankLedger/`. Cite it when the mapping
is non-obvious.

## When to use

- Classifying items in a Verus source (with `vero-discover`).
- Writing the translation plan (with `vero-plan`).
- Emitting Lean from Verus (with `vero-translate`).

## Output-shape recap (non-negotiable)

Per source module, translate emits:

- `<Project>/Impl/<Module>.lean` — types + `abbrev <Fn>Sig` per API +
  `def Bank.<fn> : Bank.<Fn>Sig := <translated reference impl>` in
  `code` / `code_aux` markers. `!curation @review v1` annotations.
- `<Project>/Spec/<Module>.lean` — `def spec_<…> (impl : RepoImpl) :
  Prop := …` only. Frozen, no markers.
- Bundle.lean, Harness.lean, Test.lean — shared, once per benchmark.

See `.claude/skills/vero-translate/SKILL.md` for file templates.

## Verus fn modes → Lean classification

Verus declares every `fn` as `exec`, `spec`, or `proof`.

| Verus | Lean artifact | Markers? |
|---|---|---|
| `exec fn` (an API) | `def Bank.<fn> : Bank.<FnSig> := <translated reference impl>` in Impl | **Yes** — `code` / `code_aux` |
| `exec fn` (helper, not an API) | Full body in Impl | No |
| `spec fn` (vocabulary) | `def <name> : <type> := …` in Impl or Spec helpers; full body | No |
| `proof fn` / `lemma` (property worth tracking) | `spec_<name>` entry → `def spec_<name>` in Spec | No (Spec frozen) |
| `proof fn` (pure proof helper) | Drop from plan — becomes `proof_aux` downstream | — |
| `#[verifier::external_body]` | `opaque` in Impl; axiomatize | No |
| `axiom` macro | `axiom <name> : <type>` near the related opaque | No |
| `#[test]` | `#guard` in `Test.lean` | No |

**Classify by role.** A `spec fn` describing an invariant →
vocabulary, no markers. A `proof fn` capturing a postcondition →
`spec_*` entry.

## Type mapping

| Verus | Lean 4 |
|---|---|
| `u64` / `u32` / `u8` | `Nat` (usually) |
| `i64` / `i32` | `Int` |
| `bool` | `Bool` |
| `String` | `String` |
| `Vec<T>` | `List T` |
| `Seq<T>` (spec-only) | `List T` |
| `Map<K, V>` (spec-only) | `List (K × V)` with uniqueness spec |
| `Set<T>` (spec-only) | `List T` with uniqueness spec |
| `Option<T>` | `Option T` |
| `Result<T, E>` | `Except E T` |
| `(T, U)` | `T × U` |
| `struct Foo { x: u64 }` | `structure Foo where x : Nat` |
| `enum Foo { A, B(u64) }` | `inductive Foo where \| A \| B (_ : Nat)` |

**`u64` → `Nat` policy.** Verus forces overflow bounds via
`requires`/`ensures`; Lean's `Nat` has no overflow. Prefer `Nat` and
elide overflow conditions — `#guard` tests still pin observable
behavior. Note the divergence in the plan if the curator wants
explicit overflow specs.

## `Vec<T>` vs `Seq<T>` and the `@` view

In Verus, `v@` lifts `Vec<T>` to `Seq<T>` for spec reasoning:
```rust
fn push(v: &mut Vec<T>, x: T)
    ensures v@ == old(v)@.push(x)
```

In Lean, both become `List T`. The `@` view has no direct analogue —
drop it and operate on the `List` directly.

plan.json:
```json
{
  "name": "spec_push_appends",
  "nl_description": "push extends the list with the new element at the end.",
  "lean_form": "∀ (v : List T) (x : T), impl.bankLedger.push v x = v ++ [x]",
  "apis_referenced": ["push"],
  "curator_intended_truth": "prove"
}
```

## API translation pattern

Verus:
```rust
pub fn create_account(id: AccountId, ledger: Ledger) -> (r: Ledger)
    requires /* … */
    ensures  /* post */
{ … }
```

plan.json:
```json
{
  "upstream_name": "create_account",
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
  -- translated Verus exec body, not `sorry`
  ...
-- !benchmark @end code def=createAccount
```

### Partial functions

- Type-enforced: use dependent argument or `Option`.
- Caller-error explicit: `Option <return>` or `Except Err <return>`.
- Pick consistently within a benchmark.

## Spec translation pattern

### `proof fn` stating a property

```rust
proof fn deposit_preserves_sum(id: AccountId, amt: u64, l: Ledger)
    ensures sum(deposit(id, amt, l)) == sum(l) + amt
{ … }
```

plan.json:
```json
{
  "name": "spec_deposit_preserves_sum",
  "nl_description": "Depositing `amt` adds exactly `amt` to the total.",
  "lean_form": "∀ (id : AccountId) (amt : Balance) (l : Ledger), impl.bankLedger.totalAssets (impl.bankLedger.deposit id amt l) = impl.bankLedger.totalAssets l + amt",
  "apis_referenced": ["deposit", "totalAssets"],
  "curator_intended_truth": "prove"
}
```

Emitted Spec:
```lean
/-- Depositing `amt` adds exactly `amt` to the total. -/
def spec_deposit_preserves_sum (impl : RepoImpl) : Prop :=
  ∀ (id : AccountId) (amt : Balance) (l : Ledger),
    impl.bankLedger.totalAssets (impl.bankLedger.deposit id amt l) =
      impl.bankLedger.totalAssets l + amt
```

### `lemma_*` proof helper

Many auxiliary lemmas per API under Verus — in the new paradigm they
don't become separate benchmark artifacts. Drop from plan.json. The
LLM may introduce similar helpers in `proof_aux` slots downstream.

## `external_body` and opaque functions

```rust
#[verifier::external_body]
pub fn now() -> u64 { … }
```

Translate to:
```lean
opaque Bank.now : Unit → Nat

-- If Verus guarantees a postcondition:
axiom Bank.now_positive : ∀ u, Bank.now u > 0
```

Mark `opaque: true` in plan.json. No `code` markers for opaque
functions.

## Common pitfalls (see `vero-verus-pitfalls`)

- `&mut` + `old(x)@` has no Lean analogue; specs become value-passing
  `f x = …`.
- Verus `assume` clauses are red flags; surface as
  `!curation @review`.
- `decreases` clauses are proof hints; use them only when Lean needs
  termination help for the translated Impl body.
- Trait-method calls may dispatch dynamically; Lean pins to concrete
  impls via `canonical` in Harness.

Load `vero-verus-pitfalls` before translating any non-trivial item.

## Pair with

- `vero-plan` — consumes Verus classifications.
- `vero-translate` — emits Lean per the templates.
- `vero-verus-pitfalls` — Verus→Lean corner cases.
- `vero-lean-pitfalls` — universal Lean traps.
