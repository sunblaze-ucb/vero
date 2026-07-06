-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Eth20Dafny.Impl.UtilsHelpers

Core helper types and utility functions used across the Eth2 Dafny
translation. Types are fixed foundation vocabulary. Implementations are
kept in source form (frozen for this module).
-/

-- !benchmark @start global_aux
-- !benchmark @end global_aux

namespace Eth20Dafny

/--
A try-like sum type used by translated specs.
-/
inductive Try (T : Type) where
  | Success : T → Try T
  | Failure : Try T

/--
Option-like type with explicit constructors.
-/
inductive Option (T : Type) where
  | None : Option T
  | Some : T → Option T

/--
Disjoint union type.
-/
inductive Either (T : Type) where
  | Left : T → Either T
  | Right : T → Either T

/-- 
`ceil n d` computes `(n / d)` rounded up, following the Dafny helper
definition. Requires `d ≠ 0` in the original source.
-/
def ceil : Nat → Nat → Nat
  | n, d =>
    if n % d == 0 then n / d else n / d + 1

/--
Construct a list of length `k` where each entry is `t`.
-/
def timeSeq {T : Type} (t : T) : Nat → List T
  | 0 => []
  | k + 1 => t :: timeSeq t k

/--
Map function `m` over all elements in a list.
-/
def seqMap {T1 : Type} {T2 : Type} : (List T1) → (T1 → T2) → List T2
  | [], _ => []
  | x :: xs, m => m x :: seqMap xs m

end Eth20Dafny
