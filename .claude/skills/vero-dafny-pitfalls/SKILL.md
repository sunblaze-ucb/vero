---
name: vero-dafny-pitfalls
description: Load BEFORE translating any Dafny item to Lean 4 to avoid known Dafny→Lean pitfalls. Pair with vero-source-dafny and vero-lean-pitfalls.
allowed-tools: Read, Write, Edit, Bash, Grep, Glob
---

# Dafny → Lean 4 Translation Pitfalls

Issues specific to translating Dafny to Lean 4.

## 1. ghost vs Compiled Code

**Problem:** Dafny `ghost` variables/functions exist only for verification.
In Lean, there's no ghost keyword — use `noncomputable` for functions that
can't be computed, or keep them as pure spec defs.

**Dafny:**
```dafny
ghost function SeqSum(s: seq<int>): int
```

**Lean:**
```lean
-- If used only in specs/proofs:
def seqSum (s : List Int) : Int := s.foldl (· + ·) 0

-- If it references opaque types:
noncomputable def seqSum (s : List Int) : Int := s.foldl (· + ·) 0
```

**Key:** Ghost functions that are pure and have clear definitions should
have their body GIVEN. Do not leave `sorry` in curated Impl/Spec files;
use an explicit `opaque` plus trusted axiom only when the source item is
intentionally trusted or external.

## 2. method vs function

**Dafny distinction:**

| Dafny | Semantics | Lean translation |
|-------|-----------|-----------------|
| `function` | Pure, can appear in specs | `def f := body` (give body if simple) |
| `method` | Imperative, may mutate | `def f := <translated reference impl>` with `code` markers |
| `ghost method` | Proof-only imperative | usually drop, or convert stated property into a `spec_*` |
| `lemma` | Proof | benchmark obligation `def spec_* (impl : RepoImpl) : Prop`, no markers |
| `predicate` | Spec vocabulary | `def f : ... → Prop := ...`, no markers unless it is selected as an API |

## 3. seq<T> → List T

**Problem:** Dafny `seq<T>` is an immutable sequence. Map to `List T`.

**Common operations:**
```lean
-- seq<T> operations → List equivalents
-- |s|          → s.length
-- s[i]         → s.get ⟨i, h⟩  (with bound proof)
-- s[i..j]      → s.drop i |>.take (j - i)
-- s + t        → s ++ t
-- s[i := v]    → s.set ⟨i, h⟩ v
-- [v] + s      → v :: s
-- s == t       → s = t
```

## 4. map<K,V>

**Dafny maps:**
```dafny
var m: map<string, int>;
m[key]           // lookup (partial)
m[key := value]  // update
key in m         // membership
```

**Lean:**
```lean
-- For computation: use Std.HashMap
-- For proofs: use a function K → Option V

-- If the map is used in computable code:
def MyMap (K V : Type) := Std.HashMap K V

-- If only in specs:
def MyMap (K V : Type) := K → Option V
```

## 5. decreases → termination_by

**Dafny:**
```dafny
function Fib(n: nat): nat
  decreases n
```

**Lean:**
```lean
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib (n + 1) + fib n
termination_by n => n
```

For API reference implementations, add `termination_by` / `decreasing_by`
when Lean cannot infer termination. The downstream LLM-facing scaffold may
replace marker bodies with `sorry`, but the curated source should build with
the real body.

## 6. multiset and set

**Dafny `multiset<T>`:** Use `List T` and reason about permutations,
or `Multiset T` from Mathlib if available.

**Dafny `set<T>`:** Use `Finset T` for finite sets, or `Set T` for
mathematical sets in proofs.

## 7. ensures with Multiple Return Values

**Dafny:**
```dafny
method Divide(a: int, b: int) returns (q: int, r: int)
  requires b > 0
  ensures a == q * b + r
  ensures 0 <= r < b
```

**Lean:** Use a product type:
```lean
def divide (a b : Int) : Int × Int :=
  (a / b, a % b)

def divide_spec (a b : Int) : Prop :=
  b > 0 →
  let (q, r) := divide a b
  a = q * b + r ∧ 0 ≤ r ∧ r < b
```

## 8. Dafny Traits and Classes

**Dafny:**
```dafny
trait Comparable {
  function CompareTo(other: Comparable): int
}
class MyType extends Comparable { ... }
```

**Lean:** Use type classes:
```lean
class Comparable (α : Type) where
  compareTo : α → α → Int

structure MyType where
  ...
  deriving Inhabited

instance : Comparable MyType where
  compareTo _a _b := 0  -- replace with the translated Dafny body
```

## 9. forall/exists Quantifiers

**Dafny:**
```dafny
forall i :: 0 <= i < |s| ==> s[i] > 0
exists i :: 0 <= i < |s| && s[i] == target
```

**Lean:**
```lean
∀ i, i < s.length → s.get ⟨i, by omega⟩ > 0
∃ i, ∃ (h : i < s.length), s.get ⟨i, h⟩ = target
```

## 10. Dafny's := vs Lean's :=

**Problem:** In Dafny, `:=` is assignment (mutable). In Lean, `:=` is
definition (immutable). Translate Dafny method bodies that use `:=` as
state-passing:

**Dafny:**
```dafny
method Push(s: Stack, v: int) returns (s': Stack) {
  s' := Cons(v, s);
}
```

**Lean:**
```lean
def push (s : Stack) (v : Int) : Stack :=
  Stack.cons v s
```
