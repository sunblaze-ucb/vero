import SpecialNumbers.Impl.GreatestCommonDivisor

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# SpecialNumbers.Impl.CarmichaelNumber

A Carmichael number n satisfies b^(n−1) ≡ 1 (mod n) for all b with
gcd(b,n)=1. Examples: 561, 1105, 8911.

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
Implement only the function bodies.
-/

-- !benchmark @start global_aux
/-- Binary modular exponentiation: x^y mod m. -/
private partial def modPow (x y m : Int) : Int :=
  -- @review human: termination via y / 2 decreasing (binary exponentiation)
  if y == 0 then 1
  else
    let temp := (modPow x (y / 2) m) % m
    let temp := (temp * temp) % m
    if y % 2 == 1 then (temp * x) % m else temp
-- !benchmark @end global_aux

namespace SpecialNumbers

-- ── API signatures (no markers — fixed vocabulary) ────────────

abbrev PowerSig             := Int → Int → Int → Int
abbrev IsCarmichaelNumberSig := Int → Bool

end SpecialNumbers

-- ── Implementation stubs (LLM task) ───────────────────────────

-- !benchmark @start code_aux def=power
-- !benchmark @end code_aux def=power

def SpecialNumbers.power : SpecialNumbers.PowerSig :=
-- !benchmark @start code def=power
  fun x y m => modPow x y m
-- !benchmark @end code def=power

-- !benchmark @start code_aux def=is_carmichael_number
-- !benchmark @end code_aux def=is_carmichael_number

def SpecialNumbers.is_carmichael_number : SpecialNumbers.IsCarmichaelNumberSig :=
-- !benchmark @start code def=is_carmichael_number
  fun n =>
    if n ≤ 3 then false
    else
      -- Check all b in [2, n-1] with gcd(b, n) = 1
      (List.range' 2 (n.toNat - 2)).all (fun b =>
        let b := (b : Int)
        SpecialNumbers.greatest_common_divisor b n != 1 ||
        modPow b (n - 1) n == 1)
-- !benchmark @end code def=is_carmichael_number
