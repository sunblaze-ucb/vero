-- !benchmark @start imports
-- !benchmark @end imports

/-!
# SpecialNumbers.Impl.PerfectNumber

A perfect number equals the sum of its proper divisors (excluding
itself). Examples: 6 (1+2+3), 28, 496, 8128.

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
Implement only the function bodies.
-/

-- !benchmark @start global_aux
-- !benchmark @end global_aux

namespace SpecialNumbers

-- ── API signatures (no markers — fixed vocabulary) ────────────

abbrev PerfectSig := Int → Bool

end SpecialNumbers

-- ── Implementation stubs (LLM task) ───────────────────────────

-- !benchmark @start code_aux def=perfect
-- !benchmark @end code_aux def=perfect

def SpecialNumbers.perfect : SpecialNumbers.PerfectSig :=
-- !benchmark @start code def=perfect
  fun number =>
    if number <= 0 then false
    else
      -- sum of divisors in [1, number/2]
      let half := (number / 2).toNat
      let total := (List.range' 1 half).foldl
        (fun (acc : Int) (i : Nat) =>
          if number % (i : Int) == 0 then acc + (i : Int) else acc)
        (0 : Int)
      total == number
-- !benchmark @end code def=perfect
