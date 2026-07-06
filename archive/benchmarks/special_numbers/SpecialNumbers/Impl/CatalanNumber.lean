-- !benchmark @start imports
-- !benchmark @end imports

/-!
# SpecialNumbers.Impl.CatalanNumber

The nth Catalan number, computed iteratively via the product formula
C(n) = ∏_{i=1}^{n-1} (4i − 2) / (i + 1). 1-indexed: C(1)=1, C(2)=1,
C(3)=2, C(4)=5, C(5)=14, …

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
Implement only the function bodies.
-/

-- !benchmark @start global_aux
-- !benchmark @end global_aux

namespace SpecialNumbers

-- ── API signatures (no markers — fixed vocabulary) ────────────

abbrev CatalanSig := Int → Int

end SpecialNumbers

-- ── Implementation stubs (LLM task) ───────────────────────────

-- !benchmark @start code_aux def=catalan
-- !benchmark @end code_aux def=catalan

def SpecialNumbers.catalan : SpecialNumbers.CatalanSig :=
-- !benchmark @start code def=catalan
  fun number =>
    if number < 1 then 0  -- Python raises ValueError; return 0 as sentinel
    else
      -- Iterative: C = ∏_{i=1}^{number-1} (4i-2) / (i+1)
      let steps := number.toNat - 1
      (List.range' 1 steps).foldl
        (fun (curr : Int) (i : Nat) =>
          let i := (i : Int)
          curr * (4 * i - 2) / (i + 1))
        1
-- !benchmark @end code def=catalan
