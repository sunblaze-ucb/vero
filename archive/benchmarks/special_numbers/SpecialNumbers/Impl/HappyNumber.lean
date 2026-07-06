-- !benchmark @start imports
-- !benchmark @end imports

/-!
# SpecialNumbers.Impl.HappyNumber

A happy number eventually reaches 1 when repeatedly replaced by the
sum of squares of its decimal digits. Non-happy numbers cycle.

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
Implement only the function bodies.
-/

-- !benchmark @start global_aux
/-- Sum of squares of decimal digits of n. -/
private partial def digitSqSum (n : Nat) : Nat :=
  -- @review human: termination via n / 10 < n for n > 0
  if n == 0 then 0
  else (n % 10) * (n % 10) + digitSqSum (n / 10)

/-- Detect whether n eventually reaches 1 (happy) or cycles. -/
private partial def happyLoop (n : Nat) (seen : List Nat) : Bool :=
  -- @review human: termination via Floyd's tortoise-and-hare or finite cycle detection;
  -- non-happy numbers always cycle through a known finite set.
  if n == 1 then true
  else if seen.contains n then false
  else happyLoop (digitSqSum n) (n :: seen)
-- !benchmark @end global_aux

namespace SpecialNumbers

-- ── API signatures (no markers — fixed vocabulary) ────────────

abbrev IsHappyNumberSig := Int → Bool

end SpecialNumbers

-- ── Implementation stubs (LLM task) ───────────────────────────

-- !benchmark @start code_aux def=is_happy_number
-- !benchmark @end code_aux def=is_happy_number

def SpecialNumbers.is_happy_number : SpecialNumbers.IsHappyNumberSig :=
-- !benchmark @start code def=is_happy_number
  fun number =>
    if number <= 0 then false
    else happyLoop number.toNat []
-- !benchmark @end code def=is_happy_number
