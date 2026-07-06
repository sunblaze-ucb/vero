-- !benchmark @start imports
-- !benchmark @end imports

/-!
# SpecialNumbers.Impl.PronicNumber

A pronic (oblong) number has the form n·(n+1): 0, 2, 6, 12, 20, 30, …
Checked via integer square root: ⌊√n⌋·(⌊√n⌋+1) == n.

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
Implement only the function bodies.
-/

-- !benchmark @start global_aux
/-- Integer square root: largest m such that m*m ≤ n. Newton's method. -/
private partial def isqrt (n x : Nat) : Nat :=
  -- @review human: Newton's method terminates because (x + n/x)/2 < x
  -- whenever x > sqrt(n); converges in O(log n) steps.
  let next := (x + n / x) / 2
  if next >= x then x else isqrt n next
-- !benchmark @end global_aux

namespace SpecialNumbers

-- ── API signatures (no markers — fixed vocabulary) ────────────

abbrev IsPronicSig := Int → Bool

end SpecialNumbers

-- ── Implementation stubs (LLM task) ───────────────────────────

-- !benchmark @start code_aux def=is_pronic
-- !benchmark @end code_aux def=is_pronic

def SpecialNumbers.is_pronic : SpecialNumbers.IsPronicSig :=
-- !benchmark @start code def=is_pronic
  fun number =>
    if number < 0 then false
    else if number % 2 == 1 then false  -- pronic numbers are always even
    else if number == 0 then true       -- 0 = 0 * 1
    else
      let n := number.toNat
      -- sq = floor(sqrt(n))
      let sq := isqrt n (n / 2 + 1)
      -- Check sq*(sq+1) == n, or (sq+1)*(sq+2) == n (in case Newton undershoots)
      n == sq * (sq + 1) || n == (sq + 1) * (sq + 2)
-- !benchmark @end code def=is_pronic
