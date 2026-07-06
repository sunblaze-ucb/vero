-- !benchmark @start imports
-- !benchmark @end imports

/-!
# SpecialNumbers.Impl.HexagonalNumber

The nth hexagonal number is H(n) = n·(2n−1). Defined for positive
integers only.

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
Implement only the function bodies.
-/

-- !benchmark @start global_aux
-- !benchmark @end global_aux

namespace SpecialNumbers

-- ── API signatures (no markers — fixed vocabulary) ────────────

abbrev HexagonalSig := Int → Int

end SpecialNumbers

-- ── Implementation stubs (LLM task) ───────────────────────────

-- !benchmark @start code_aux def=hexagonal
-- !benchmark @end code_aux def=hexagonal

def SpecialNumbers.hexagonal : SpecialNumbers.HexagonalSig :=
-- !benchmark @start code def=hexagonal
  fun number =>
    if number < 1 then 0  -- Python raises ValueError
    else number * (2 * number - 1)
-- !benchmark @end code def=hexagonal
