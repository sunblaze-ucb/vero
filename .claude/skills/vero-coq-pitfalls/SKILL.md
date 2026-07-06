---
name: vero-coq-pitfalls
description: Load BEFORE translating any Coq item to Lean 4 to avoid known Coq→Lean pitfalls. Pair with vero-source-coq and vero-lean-pitfalls.
allowed-tools: Read, Write, Edit, Bash, Grep, Glob
---

# Coq → Lean 4 Translation Pitfalls

Issues specific to translating Coq to Lean 4.

## 1. Fixpoint → def with termination_by

**Coq:**
```coq
Fixpoint length {A : Type} (l : list A) : nat :=
  match l with
  | nil => 0
  | cons _ t => S (length t)
  end.
```

**Lean:**
```lean
def length {α : Type} (l : List α) : Nat :=
  match l with
  | [] => 0
  | _ :: t => 1 + length t
```

Lean can often infer structural recursion automatically. Add
`termination_by` only when needed:
```lean
termination_by l.length
```

For curated API reference implementations, add `termination_by` when
Lean cannot infer structural recursion. The LLM-facing `sorry` is
introduced later by pre-agent materialization, not in the curated source.

## 2. Inductive / Record → inductive / structure

**Coq:**
```coq
Inductive tree (A : Type) : Type :=
| Leaf : tree A
| Node : A -> tree A -> tree A -> tree A.

Record point := { x : Z; y : Z }.
```

**Lean:**
```lean
inductive Tree (α : Type) where
  | leaf : Tree α
  | node : α → Tree α → Tree α → Tree α
  deriving Inhabited, Repr

structure Point where
  x : Int
  y : Int
  deriving Inhabited, Repr
```

**Key differences:**
- Coq constructors are top-level; Lean constructors are namespaced
  (`Tree.leaf` not just `leaf`)
- Coq `Record` becomes Lean `structure` (with field projection)
- Add `deriving Inhabited` when default values are actually needed by
  translated code/tests; do not add instances just because a downstream
  proof might want them.

## 3. Prop / Set / Type Universe Mapping

| Coq | Lean | Notes |
|-----|------|-------|
| `Prop` | `Prop` | Direct correspondence |
| `Set` | `Type` | Coq `Set` ≈ Lean `Type 0` |
| `Type` | `Type 1` | Coq `Type` is one level higher than `Set` |
| `bool` | `Bool` | Computational booleans |
| `nat` | `Nat` | Natural numbers |
| `Z` | `Int` | Integers |

**Common mistake:** Translating Coq `Set` as Lean `Set` — Lean's `Set α`
is `α → Prop` (a predicate), NOT a universe level. Use `Type` instead.

## 4. Section Variables

**Coq:**
```coq
Section MySection.
  Variable A : Type.
  Variable f : A -> A.

  Definition apply_twice (x : A) : A := f (f x).
End MySection.
(* apply_twice : forall A : Type, (A -> A) -> A -> A *)
```

**Lean:**
```lean
-- Option 1: explicit parameters
def applyTwice {α : Type} (f : α → α) (x : α) : α := f (f x)

-- Option 2: section variables (closer to Coq style)
section MySection
  variable {α : Type}
  variable (f : α → α)

  def applyTwice (x : α) : α := f (f x)
end MySection
```

**Key:** Coq `Variable` in a `Section` becomes implicit after `End`.
In Lean, use `variable` in a `section` for the same effect.

## 5. Coq Tactics → Lean Tactics

| Coq tactic | Lean equivalent | Notes |
|-----------|-----------------|-------|
| `intro` | `intro` | Same |
| `apply` | `apply` | Same |
| `exact` | `exact` | Same |
| `rewrite` | `rw` | Lean uses `rw` |
| `simpl` | `simp` | Different behavior — Lean `simp` is more powerful |
| `unfold` | `unfold` | Same |
| `destruct` | `cases` or `match` | |
| `induction` | `induction` | Same |
| `omega` | `omega` | Same (for linear arithmetic) |
| `ring` | `ring` | Same |
| `auto` | `simp` or `aesop` | No direct equivalent |
| `trivial` | `trivial` | Same |
| `reflexivity` | `rfl` | Lean uses `rfl` |
| `split` | `constructor` or `And.intro` | |
| `left`/`right` | `left`/`right` | Same |
| `exists` | `use` or `exact ⟨...⟩` | |
| `assert` | `have` | |
| `pose` | `let` | |
| `lia` | `omega` | Linear integer arithmetic |

**Curation rule:** source proofs become benchmark specs, not
curation-time Lean theorem proofs. Use this tactic mapping only when
you are translating proof-relevant vocabulary or checking an auxiliary
lemma by hand.

## 6. Program / Program Fixpoint

**Problem:** Coq `Program` allows partial definitions with obligations.
In Lean, these become regular `def` with proof obligations as separate
theorems.

**Coq:**
```coq
Program Fixpoint merge (l1 l2 : list nat) {measure (length l1 + length l2)} :=
  ...
```

**Lean:**
```lean
def merge (l1 l2 : List Nat) : List Nat :=
-- !benchmark @start code def=merge
  -- translated merge body
  ...
-- !benchmark @end code def=merge
termination_by l1.length + l2.length
```

## 7. Module System

**Coq:**
```coq
Module Stack.
  Definition t := list nat.
  Definition push := cons.
End Stack.
```

**Lean:**
```lean
namespace Stack
  def T := List Nat
  def push := List.cons
end Stack
```

**Coq `Module Type`** (interfaces) → Lean `class` or `structure`:
```lean
class StackInterface (S : Type) where
  push : S → Nat → S
  pop : S → Option (Nat × S)
```

## 8. Notation and Coercions

**Problem:** Coq notations (`` `( ... ) ``) and coercions don't transfer.

**Fix:** Replace Coq notations with explicit Lean function calls. If
the notation is widely used, define a Lean `notation` or `scoped notation`:
```lean
scoped notation "⟦" x "⟧" => interpret x
```

For API reference implementations, prefer explicit function calls unless
the notation materially improves readability and is used consistently.

## 9. Dependent Types

**Coq:**
```coq
Definition safe_head {A} (l : list A) (H : l <> nil) : A := ...
```

**Lean:**
```lean
def safeHead {α : Type} (l : List α) (h : l ≠ []) : α :=
  match l with
  | [] => False.elim (h rfl)
  | x :: _ => x
```

The dependent proof parameter `h : l ≠ []` transfers directly.

## 10. Extraction vs Compilation

**Problem:** Coq uses extraction (`Extraction`) to produce OCaml/Haskell.
Lean compiles directly. Functions marked `Extraction Inline` or with
`Extract Constant` have no Lean equivalent.

**Fix:**
- `Extract Constant f => "..."` → `opaque f ...` (external boundary)
- `Extraction Inline f` → just define `f` normally (Lean inlines via compiler)
- If the extracted constant is a standard operation, map to Lean stdlib
