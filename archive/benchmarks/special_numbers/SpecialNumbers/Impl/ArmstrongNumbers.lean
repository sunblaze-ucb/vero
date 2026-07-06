-- !benchmark @start imports
-- !benchmark @end imports

/-!
# SpecialNumbers.Impl.ArmstrongNumbers

Armstrong (Narcissistic, Pluperfect) numbers. A number n is Armstrong if
n = Σ dᵢᵏ where dᵢ are its decimal digits and k = number of digits.

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
Implement only the function bodies.
-/

-- !benchmark @start global_aux
/-- Extract decimal digits of n (least-significant first) as a list of Nat.
    Returns [] for n = 0. -/
private partial def posDigits (n : Nat) : List Nat :=
  -- @review human: termination via n / 10 < n for n > 0 (Nat division)
  if n == 0 then []
  else (n % 10) :: posDigits (n / 10)
-- !benchmark @end global_aux

namespace SpecialNumbers

-- ── API signatures (no markers — fixed vocabulary) ────────────

abbrev ArmstrongNumberSig  := Int → Bool
abbrev PluperfectNumberSig := Int → Bool
abbrev NarcissisticNumberSig := Int → Bool

end SpecialNumbers

-- ── Implementation stubs (LLM task) ───────────────────────────

-- !benchmark @start code_aux def=armstrong_number
-- !benchmark @end code_aux def=armstrong_number

def SpecialNumbers.armstrong_number : SpecialNumbers.ArmstrongNumberSig :=
-- !benchmark @start code def=armstrong_number
  fun n =>
    if n < 1 then false
    else
      let ds := posDigits n.natAbs
      let k  := ds.length
      n == ds.foldl (fun (acc : Int) (d : Nat) => acc + (d : Int) ^ k) 0
-- !benchmark @end code def=armstrong_number

-- !benchmark @start code_aux def=pluperfect_number
-- !benchmark @end code_aux def=pluperfect_number

def SpecialNumbers.pluperfect_number : SpecialNumbers.PluperfectNumberSig :=
-- !benchmark @start code def=pluperfect_number
  fun n =>
    -- Equivalent to armstrong_number: uses digit histogram then Σ cnt_i * i^k.
    -- Since Σ cnt_i * i^k = Σ_{each digit d} d^k, same as armstrong_number.
    if n < 1 then false
    else
      let ds := posDigits n.natAbs
      let k  := ds.length
      n == ds.foldl (fun (acc : Int) (d : Nat) => acc + (d : Int) ^ k) 0
-- !benchmark @end code def=pluperfect_number

-- !benchmark @start code_aux def=narcissistic_number
-- !benchmark @end code_aux def=narcissistic_number

def SpecialNumbers.narcissistic_number : SpecialNumbers.NarcissisticNumberSig :=
-- !benchmark @start code def=narcissistic_number
  fun n =>
    -- Python iterates str(n) characters; equivalent to posDigits.
    if n < 1 then false
    else
      let ds := posDigits n.natAbs
      let k  := ds.length
      n == ds.foldl (fun (acc : Int) (d : Nat) => acc + (d : Int) ^ k) 0
-- !benchmark @end code def=narcissistic_number
