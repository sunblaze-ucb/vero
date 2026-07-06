-- !benchmark @start imports
-- !benchmark @end imports

/-!
# SpecialNumbers.Impl.AutomorphicNumber

An automorphic number is one whose square ends in the same digits as
the number itself. E.g. 5² = 25 ends in 5, 76² = 5776 ends in 76.

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
Implement only the function bodies.
-/

-- !benchmark @start global_aux
/-- Check digit-by-digit from the right that n and sq share the same digits. -/
private partial def automorphicCheck (n sq : Int) : Bool :=
  -- @review human: termination via n / 10 decreasing toward 0
  if n == 0 then true
  else if n % 10 != sq % 10 then false
  else automorphicCheck (n / 10) (sq / 10)
-- !benchmark @end global_aux

namespace SpecialNumbers

-- ── API signatures (no markers — fixed vocabulary) ────────────

abbrev IsAutomorphicNumberSig := Int → Bool

end SpecialNumbers

-- ── Implementation stubs (LLM task) ───────────────────────────

-- !benchmark @start code_aux def=is_automorphic_number
-- !benchmark @end code_aux def=is_automorphic_number

def SpecialNumbers.is_automorphic_number : SpecialNumbers.IsAutomorphicNumberSig :=
-- !benchmark @start code def=is_automorphic_number
  fun number =>
    if number < 0 then false
    else automorphicCheck number (number * number)
-- !benchmark @end code def=is_automorphic_number
