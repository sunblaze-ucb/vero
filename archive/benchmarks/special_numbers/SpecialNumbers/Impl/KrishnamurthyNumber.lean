-- !benchmark @start imports
-- !benchmark @end imports

/-!
# SpecialNumbers.Impl.KrishnamurthyNumber

A Krishnamurthy number (Peterson number) equals the sum of factorials
of its digits. Examples: 1 (1!), 2 (2!), 145 (1!+4!+5!), 40585.

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
Implement only the function bodies.
-/

-- !benchmark @start global_aux
/-- Loop: sum factorials of each decimal digit of n_. -/
private partial def digitFactLoop (fact : Int → Int) (acc n_ : Int) : Int :=
  -- @review human: termination via n_ / 10 → 0 (strips last digit each step)
  if n_ <= 0 then acc
  else digitFactLoop fact (acc + fact (n_ % 10)) (n_ / 10)
-- !benchmark @end global_aux

namespace SpecialNumbers

-- ── API signatures (no markers — fixed vocabulary) ────────────

abbrev FactorialSig     := Int → Int
abbrev KrishnamurthySig := Int → Bool

end SpecialNumbers

-- ── Implementation stubs (LLM task) ───────────────────────────

-- !benchmark @start code_aux def=factorial
-- !benchmark @end code_aux def=factorial

def SpecialNumbers.factorial : SpecialNumbers.FactorialSig :=
-- !benchmark @start code def=factorial
  fun digit =>
    if digit <= 1 then 1
    else
      -- Iterative product: 2 * 3 * … * digit (range' 2 (digit-1) = [2,…,digit])
      let steps := digit.toNat - 1
      (List.range' 2 steps).foldl (fun (acc : Int) (i : Nat) => acc * (i : Int)) 1
-- !benchmark @end code def=factorial

-- !benchmark @start code_aux def=krishnamurthy
-- !benchmark @end code_aux def=krishnamurthy

def SpecialNumbers.krishnamurthy : SpecialNumbers.KrishnamurthySig :=
-- !benchmark @start code def=krishnamurthy
  fun number =>
    digitFactLoop SpecialNumbers.factorial 0 number == number
-- !benchmark @end code def=krishnamurthy
