-- !benchmark @start imports
-- !benchmark @end imports

/-!
# SpecialNumbers.Impl.GreatestCommonDivisor

Greatest Common Divisor algorithms. Two implementations: recursive
(Euclidean algorithm) and iterative (loop-based).

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
Implement only the function bodies.
-/

-- !benchmark @start global_aux
-- @review human: termination via Int.natAbs a decreasing (Euclidean algorithm,
-- floor-division modulo ensures |b % a| < |a| when a ≠ 0)
private partial def gcdRec (a b : Int) : Int :=
  if a == 0 then (b.natAbs : Int)
  else gcdRec (Int.fmod b a) a

-- @review human: termination via Int.natAbs y decreasing (Euclidean algorithm)
private partial def gcdIter (x y : Int) : Int :=
  if y == 0 then (x.natAbs : Int)
  else gcdIter y (Int.fmod x y)
-- !benchmark @end global_aux

namespace SpecialNumbers

-- ── API signatures (no markers — fixed vocabulary) ────────────

abbrev GreatestCommonDivisorSig := Int → Int → Int
abbrev GcdByIterativeSig        := Int → Int → Int

end SpecialNumbers

-- ── Implementation stubs (LLM task) ───────────────────────────

-- !benchmark @start code_aux def=greatest_common_divisor
-- !benchmark @end code_aux def=greatest_common_divisor

def SpecialNumbers.greatest_common_divisor : SpecialNumbers.GreatestCommonDivisorSig :=
-- !benchmark @start code def=greatest_common_divisor
  fun a b => gcdRec a b
-- !benchmark @end code def=greatest_common_divisor

-- !benchmark @start code_aux def=gcd_by_iterative
-- !benchmark @end code_aux def=gcd_by_iterative

def SpecialNumbers.gcd_by_iterative : SpecialNumbers.GcdByIterativeSig :=
-- !benchmark @start code def=gcd_by_iterative
  fun x y => gcdIter x y
-- !benchmark @end code def=gcd_by_iterative
