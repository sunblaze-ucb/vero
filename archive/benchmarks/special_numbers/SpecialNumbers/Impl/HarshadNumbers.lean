-- !benchmark @start imports
-- !benchmark @end imports

/-!
# SpecialNumbers.Impl.HarshadNumbers

A Harshad number in base b is divisible by the sum of its digits in
base b. This module provides base-conversion utilities and Harshad checks.

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
Implement only the function bodies.
-/

-- !benchmark @start global_aux
private def digitAlphabet : List Char :=
  "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ".toList

/-- Numeric value of a single digit character (A=10, B=11, …). -/
private def charDigitVal (c : Char) : Nat :=
  digitAlphabet.findIdx (· == c)

/-- Parse a base-b string back to an Int. -/
private def parseBase (s : String) (base : Int) : Int :=
  s.toList.foldl (fun (acc : Int) c => acc * base + (charDigitVal c : Int)) 0

/-- Convert a non-negative Int to a string in the given base (2–36). -/
private partial def convertBase (n base : Int) (acc : String) : String :=
  -- @review human: termination via n / base < n for n > 0, base ≥ 2
  if n == 0 then acc
  else
    let rem := (n % base).toNat
    let c := digitAlphabet.getD rem '?'
    convertBase (n / base) base (c.toString ++ acc)
-- !benchmark @end global_aux

namespace SpecialNumbers

-- ── API signatures (no markers — fixed vocabulary) ────────────

abbrev IntToBaseSig              := Int → Int → String
abbrev SumOfDigitsSig            := Int → Int → String
abbrev HarshadNumbersInBaseSig   := Int → Int → List String
abbrev IsHarshadNumberInBaseSig  := Int → Int → Bool

end SpecialNumbers

-- ── Implementation stubs (LLM task) ───────────────────────────

-- !benchmark @start code_aux def=int_to_base
-- !benchmark @end code_aux def=int_to_base

def SpecialNumbers.int_to_base : SpecialNumbers.IntToBaseSig :=
-- !benchmark @start code def=int_to_base
  fun number base =>
    if base < 2 || base > 36 then ""
    else if number < 0 then ""
    else if number == 0 then "0"
    else convertBase number base ""
-- !benchmark @end code def=int_to_base

-- !benchmark @start code_aux def=sum_of_digits
-- !benchmark @end code_aux def=sum_of_digits

def SpecialNumbers.sum_of_digits : SpecialNumbers.SumOfDigitsSig :=
-- !benchmark @start code def=sum_of_digits
  fun num base =>
    if base < 2 || base > 36 then ""
    else
      let numStr := SpecialNumbers.int_to_base num base
      let total : Int := numStr.toList.foldl (fun (acc : Int) c => acc + (charDigitVal c : Int)) 0
      SpecialNumbers.int_to_base total base
-- !benchmark @end code def=sum_of_digits

-- !benchmark @start code_aux def=harshad_numbers_in_base
-- !benchmark @end code_aux def=harshad_numbers_in_base

def SpecialNumbers.harshad_numbers_in_base : SpecialNumbers.HarshadNumbersInBaseSig :=
-- !benchmark @start code def=harshad_numbers_in_base
  fun limit base =>
    if base < 2 || base > 36 then []
    else if limit < 0 then []
    else
      let len := if limit.toNat > 0 then limit.toNat - 1 else 0
      (List.range' 1 len).filterMap (fun (i : Nat) =>
        let iInt : Int := i
        let s := SpecialNumbers.sum_of_digits iInt base
        let sv : Int := parseBase s base
        if sv > 0 && iInt % sv == 0 then
          some (SpecialNumbers.int_to_base iInt base)
        else none)
-- !benchmark @end code def=harshad_numbers_in_base

-- !benchmark @start code_aux def=is_harshad_number_in_base
-- !benchmark @end code_aux def=is_harshad_number_in_base

def SpecialNumbers.is_harshad_number_in_base : SpecialNumbers.IsHarshadNumberInBaseSig :=
-- !benchmark @start code def=is_harshad_number_in_base
  fun num base =>
    if base < 2 || base > 36 then false
    else if num < 0 then false
    else
      let d := SpecialNumbers.sum_of_digits num base
      let dv : Int := parseBase d base
      dv > 0 && num % dv == 0
-- !benchmark @end code def=is_harshad_number_in_base
