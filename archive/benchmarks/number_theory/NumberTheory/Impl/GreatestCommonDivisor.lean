-- !benchmark @start imports
-- !benchmark @end imports

/-!
# NumberTheory.Impl.GreatestCommonDivisor

Greatest Common Divisor implementations.

Source: `maths/greatest_common_divisor.py` from TheAlgorithms/Python.
Provides two implementations: a recursive one and an iterative one.
Both return the non-negative GCD, handling negative inputs via `Int.natAbs`.

gcd(a, b) = gcd(a, -b) = gcd(-a, b) = gcd(-a, -b) by definition of divisibility.

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
Implement only the function bodies.
-/

-- !benchmark @start global_aux
-- !benchmark @end global_aux

namespace NT

-- ── API signatures (no markers — fixed vocabulary) ────────────────────

abbrev GreatestCommonDivisorSig := Int → Int → Int
abbrev GcdByIterativeSig        := Int → Int → Int

end NT

-- ── Implementations ───────────────────────────────────────────────────

-- !benchmark @start code_aux def=greatest_common_divisor
-- !benchmark @end code_aux def=greatest_common_divisor

partial def NT.greatest_common_divisor : NT.GreatestCommonDivisorSig :=
-- !benchmark @start code def=greatest_common_divisor
  -- @review human: termination via |a| strictly decreasing under Euclidean algorithm on Int
  fun a b =>
    if a == 0 then (Int.natAbs b : Int)
    else NT.greatest_common_divisor (b % a) a
-- !benchmark @end code def=greatest_common_divisor

-- !benchmark @start code_aux def=gcd_by_iterative
-- Iterative tail-recursive helper; partial because termination over Int requires proof.
-- @review human: termination via |y| strictly decreasing under Euclidean algorithm on Int
private partial def gcdIter (x y : Int) : Int :=
  if y == 0 then (Int.natAbs x : Int)
  else gcdIter y (x % y)
-- !benchmark @end code_aux def=gcd_by_iterative

def NT.gcd_by_iterative : NT.GcdByIterativeSig :=
-- !benchmark @start code def=gcd_by_iterative
  fun x y => gcdIter x y
-- !benchmark @end code def=gcd_by_iterative
