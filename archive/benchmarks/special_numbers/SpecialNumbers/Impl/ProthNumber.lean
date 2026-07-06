-- !benchmark @start imports
-- !benchmark @end imports

/-!
# SpecialNumbers.Impl.ProthNumber

Proth numbers are of the form k·2^n + 1 where k < 2^n.
The sequence is 3, 5, 9, 13, 17, 25, 33, 41, 49, 57, …
Given a 1-based index, returns that Proth number.
Returns 0 for invalid (non-positive) input.

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
Implement only the function bodies.
-/

-- !benchmark @start global_aux
/-- Floor of log base 2: largest p such that 2^p ≤ n. Returns 0 for n ≤ 1.
    @review human: terminates because n / 2 < n for n > 1. -/
private partial def log2floor (n : Nat) : Nat :=
  if n <= 1 then 0 else log2floor (n / 2) + 1

/-- Internal state for Proth number generation. -/
private structure ProthState where
  arr        : Array Nat
  prothIndex : Nat
  increment  : Nat

/-- Perform one outer block of Proth number generation. -/
private def prothBlock (s : ProthState) (block : Nat) : ProthState :=
  -- @review human: inner loop runs s.increment times for each block
  let s' := (List.range s.increment).foldl
    (fun (acc : ProthState) (_ : Nat) =>
      let newVal := 2 ^ (block + 1) + acc.arr.getD (acc.prothIndex - 1) 0
      { acc with arr := acc.arr.push newVal, prothIndex := acc.prothIndex + 1 })
    s
  { s' with increment := s'.increment * 2 }
-- !benchmark @end global_aux

namespace SpecialNumbers

-- ── API signatures (no markers — fixed vocabulary) ────────────

abbrev ProthSig := Int → Int

end SpecialNumbers

-- ── Implementation stubs (LLM task) ───────────────────────────

-- !benchmark @start code_aux def=proth
-- !benchmark @end code_aux def=proth

def SpecialNumbers.proth : SpecialNumbers.ProthSig :=
-- !benchmark @start code def=proth
  fun number =>
    if number <= 0 then 0
    else if number == 1 then 3
    else if number == 2 then 5
    else
      let n := number.toNat
      -- block_index = floor(log2(n // 3)) + 2
      let blockIndex := log2floor ((n / 3).max 1) + 2
      let init : ProthState := { arr := #[3, 5], prothIndex := 2, increment := 3 }
      -- outer loop: range(1, block_index) = blocks 1, 2, …, blockIndex-1
      let final := (List.range' 1 (blockIndex - 1)).foldl prothBlock init
      (final.arr.getD (n - 1) 0 : Nat)
-- !benchmark @end code def=proth
