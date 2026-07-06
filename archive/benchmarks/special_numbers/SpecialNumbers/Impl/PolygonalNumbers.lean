-- !benchmark @start imports
-- !benchmark @end imports

/-!
# SpecialNumbers.Impl.PolygonalNumbers

The nth s-gonal number: P(s, n) = ((s−2)·n² − (s−4)·n) / 2.
Requires n ≥ 0 and s ≥ 3.

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
Implement only the function bodies.
-/

-- !benchmark @start global_aux
-- !benchmark @end global_aux

namespace SpecialNumbers

-- ── API signatures (no markers — fixed vocabulary) ────────────

abbrev PolygonalNumSig := Int → Int → Int

end SpecialNumbers

-- ── Implementation stubs (LLM task) ───────────────────────────

-- !benchmark @start code_aux def=polygonal_num
-- !benchmark @end code_aux def=polygonal_num

def SpecialNumbers.polygonal_num : SpecialNumbers.PolygonalNumSig :=
-- !benchmark @start code def=polygonal_num
  fun num sides =>
    if num < 0 || sides < 3 then 0  -- Python raises ValueError
    else ((sides - 2) * num ^ 2 - (sides - 4) * num) / 2
-- !benchmark @end code def=polygonal_num
