import NumberTheory.Impl.GreatestCommonDivisor

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# NumberTheory.Impl.LeastCommonMultiple

Least Common Multiple implementations.

Source: `maths/least_common_multiple.py` from TheAlgorithms/Python.
Provides two implementations:
- `least_common_multiple_slow`: brute-force iteration starting from max(a,b).
- `least_common_multiple_fast`: GCD-based formula `(a / gcd(a,b)) * b`.

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
Implement only the function bodies.
-/

-- !benchmark @start global_aux
-- !benchmark @end global_aux

namespace NT

-- ── API signatures (no markers — fixed vocabulary) ────────────────────

abbrev LeastCommonMultipleSlowSig := Int → Int → Int
abbrev LeastCommonMultipleFastSig := Int → Int → Int

end NT

-- ── Implementations ───────────────────────────────────────────────────

-- !benchmark @start code_aux def=least_common_multiple_slow
-- Tail-recursive helper that increments by max_num until divisible by both.
-- @review human: termination via (a * b - common_mult) decreasing; partial over Int
private partial def lcmSlowAux (first_num second_num max_num common_mult : Int) : Int :=
  if common_mult % first_num == 0 && common_mult % second_num == 0 then
    common_mult
  else
    lcmSlowAux first_num second_num max_num (common_mult + max_num)
-- !benchmark @end code_aux def=least_common_multiple_slow

def NT.least_common_multiple_slow : NT.LeastCommonMultipleSlowSig :=
-- !benchmark @start code def=least_common_multiple_slow
  fun first_num second_num =>
    let max_num := if first_num >= second_num then first_num else second_num
    lcmSlowAux first_num second_num max_num max_num
-- !benchmark @end code def=least_common_multiple_slow

-- !benchmark @start code_aux def=least_common_multiple_fast
-- !benchmark @end code_aux def=least_common_multiple_fast

def NT.least_common_multiple_fast : NT.LeastCommonMultipleFastSig :=
-- !benchmark @start code def=least_common_multiple_fast
  fun first_num second_num =>
    (first_num / NT.greatest_common_divisor first_num second_num) * second_num
-- !benchmark @end code def=least_common_multiple_fast
