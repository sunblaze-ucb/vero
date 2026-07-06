-- !benchmark @start imports
-- !benchmark @end imports

/-!
# SpecialNumbers.Impl.TriangularNumbers

A triangular number counts objects arranged in an equilateral triangle.
The nth triangular number is n*(n+1)/2. Returns 0 for negative positions.

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
Implement only the function bodies.
-/

-- !benchmark @start global_aux
-- !benchmark @end global_aux

namespace SpecialNumbers

-- ── API signatures (no markers — fixed vocabulary) ────────────

abbrev TriangularNumberSig := Int → Int

end SpecialNumbers

-- ── Implementation stubs (LLM task) ───────────────────────────

-- !benchmark @start code_aux def=triangular_number
-- !benchmark @end code_aux def=triangular_number

def SpecialNumbers.triangular_number : SpecialNumbers.TriangularNumberSig :=
-- !benchmark @start code def=triangular_number
  fun position =>
    if position < 0 then 0
    else position * (position + 1) / 2
-- !benchmark @end code def=triangular_number
