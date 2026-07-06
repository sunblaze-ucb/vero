---
name: vero-source-coq
description: Load BEFORE translating Coq source (.v files) to Lean 4. Provides Coq-specific classification rules, type mappings, and patterns for mapping Coq constructs (Definition / Fixpoint / Inductive / Theorem / Module) into the ratified bundle paradigm (Impl/ + Spec/ + Bundle + Harness). Pair with vero-discover, vero-plan, vero-translate, and vero-coq-pitfalls.
allowed-tools: Read, Write, Edit, Bash, Grep, Glob
---

# VCG Source: Coq → Lean 4

Coq-specific classification and translation patterns for the ratified
curation paradigm. The **shape of the emitted Lean** is pinned by
`reference/BankLedger/` + `.claude/skills/vero-translate/SKILL.md` —
this skill teaches the *language mapping*.

Lean 4's core calculus (CIC-like + inductive families) is close to
Coq's. The main work is Module/Section → Lean namespace, tactic
divergence, and the `Prop` vs `Bool` decidability split.

## When to use

- Classifying items in a Coq source (`.v`) with `vero-discover`.
- Writing the translation plan with `vero-plan`.
- Emitting Lean from Coq with `vero-translate`.

## Output-shape recap (non-negotiable)

Per source-side Coq module (a `Section`, `Module`, or one `.v` file),
translate emits:

- `<Project>/Impl/<Module>.lean` — types + sig abbrevs + translated
  reference implementations in `code` slots.
- `<Project>/Spec/<Module>.lean` — `def spec_<…> (impl : RepoImpl) :
  Prop := …`. Frozen, no markers.
- Bundle.lean + Harness.lean + Test.lean shared across modules.

See `.claude/skills/vero-translate/SKILL.md` for file templates.

## Coq construct → Lean classification

| Coq | Lean artifact | Markers? |
|---|---|---|
| `Definition` (computable, API) | `def Bank.<fn> : Bank.<FnSig> := <translated reference impl>` | **Yes** — `code` / `code_aux` |
| `Definition` (vocabulary) | `def <name> : <type> := …` full body | No |
| `Fixpoint` (API) | Same as API `Definition`, with the translated recursive reference implementation | Yes |
| `Fixpoint` (vocabulary) | `def <name>` with full body; `termination_by` if needed | No |
| `Inductive` | `inductive <name> where \| <ctor> : <type>` | No |
| `Record` | `structure <name> where <field> : <type>` | No |
| `Class` (type class) | `class <name> where <field> : <type>` | No |
| `Theorem` / `Lemma` (property worth tracking) | `spec_<name>` in plan.json | No (Spec frozen) |
| `Theorem` / `Lemma` (proof helper only) | Drop from plan — becomes `proof_aux` downstream | — |
| `Axiom` | `axiom <name> : <type>` in Impl | No |
| `Parameter` | `axiom <name>` or `opaque` if a caller provides the impl | No |
| `Hypothesis` (inside Section) | Becomes arguments to post-`End` definitions | — |
| `Notation` | Usually elide; translate expands where used | — |
| `Scheme` (induction principles) | Skip — Lean generates them automatically | — |

**Classify by role.** A `Fixpoint` implementing `fold` (vocabulary
used by other defs) → full-body helper, no markers. A `Fixpoint` for
`push` (an API the user calls) → translated reference implementation in
a `code` slot.

## Type mapping

| Coq | Lean 4 |
|---|---|
| `nat` | `Nat` |
| `Z` | `Int` |
| `N` | `Nat` |
| `bool` | `Bool` |
| `Prop` | `Prop` |
| `string` | `String` |
| `list A` | `List A` |
| `option A` | `Option A` |
| `sum A B` | `A ⊕ B` |
| `prod A B` | `A × B` |
| `{x : A | P x}` | `{x : A // P x}` (Lean `Subtype`) |
| `A -> B` | `A → B` |
| `forall x, P x` | `∀ x, P x` |
| `exists x, P x` | `∃ x, P x` |
| `unit` | `Unit` |
| `True` / `False` (in Prop) | `True` / `False` |

`Prop` vs `Bool`: Coq often uses `bool` for decidable checks; Lean 4
has `Bool` + `Decidable` instances. Keep `Bool` returns as `Bool`;
specs can use `= true` / `= false`.

## Namespace translation

Coq's `Section` and `Module` both become Lean namespaces when needed,
but the project's **public API** lives under one umbrella namespace
(e.g. `Bank`). Individual Coq modules become *file* names under
`Impl/`, not separate Lean namespaces.

```coq
Module Account.
  Definition create_account (id : nat) (l : ledger) : ledger := …
End Account.
```

→ emitted in `Impl/Account.lean`:
```lean
namespace Bank
abbrev CreateAccountSig := AccountId → Ledger → Ledger
end Bank

def Bank.createAccount : Bank.CreateAccountSig := <translated reference impl>
```

The Coq module name `Account` determines the *file* name; the Lean
namespace is `Bank` (the API umbrella).

## API translation pattern

Coq:
```coq
Definition create_account (id : nat) (l : ledger) : ledger := …
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
  -- translated Coq body, not `sorry`
  ...
-- !benchmark @end code def=createAccount
```

### Partial functions

Coq functions are total by construction. When the source uses a
subset type (`{x : A | P x}`), translate as `Subtype`, **or** relax to
`A` + a hypothesis argument, **or** switch to `Option A` — match the
project's overall convention.

## Spec translation pattern

### `Theorem` / `Lemma` → spec entry

Coq:
```coq
Theorem deposit_preserves_sum :
  forall (id : nat) (amt : nat) (l : ledger),
    sum (deposit id amt l) = sum l + amt.
Proof. … Qed.
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

The Coq proof body is discarded — the Lean proof is materialized
per-mode downstream.

The theorem statement is not optional. If you cannot translate the Coq
proposition into a concrete Lean `Prop`, do not emit a scored
`spec_<name>` for it. Keep the item review-only/untranslated with source
provenance and a reason. Do not use a generated predicate such as
`sourceSpec`, source-token wrappers, `True`, or any other placeholder to
stand in for the theorem body.

### `Lemma` as a proof helper

Used only by other proofs (no standalone property) → drop from
plan.json. The LLM produces analogous helpers in `proof_aux` slots
downstream.

## Sections and `Implicit Type`

```coq
Section LedgerOps.
  Variable L : ledger.
  Hypothesis (HL : valid L).
  Definition deposit_safe (id amt : nat) : ledger := …
End LedgerOps.
```

After `End`, `deposit_safe` takes `L` and `HL` as explicit arguments.
Translate the *exported* (post-`End`) signature. Don't carry the
`Section` block into Lean.

## Common pitfalls (see `vero-coq-pitfalls`)

- `Prop` vs `bool` vs `Bool` — pick one for API returns; be
  consistent.
- `Program Fixpoint` / `Function` / `Equations` — translate to plain
  `def` with explicit `termination_by` if needed.
- Coercions — Coq's implicit coercions often don't survive; make
  conversions explicit in the Lean form.
- `classical` / choice axioms — flag as `!curation @review`; Lean's
  stdlib may need `Classical.choice`.

Load `vero-coq-pitfalls` before translating any non-trivial item.

## Pair with

- `vero-plan` — consumes Coq classifications.
- `vero-translate` — emits Lean per the templates.
- `vero-coq-pitfalls` — Coq→Lean corner cases.
- `vero-lean-pitfalls` — universal Lean traps.
