-- !benchmark @start imports
-- !benchmark @end imports

/-!
# SpecialNumbers.Impl.UglyNumbers

Ugly numbers are numbers whose only prime factors are 2, 3, or 5.
The sequence is 1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 15, …
Given n, returns the nth ugly number (1-indexed; returns 1 for n ≤ 0).

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
Implement only the function bodies.
-/

-- !benchmark @start global_aux
/-- Internal state for the three-pointer ugly number algorithm. -/
private structure UglyState where
  arr   : Array Nat
  i2    : Nat
  i3    : Nat
  i5    : Nat
  next2 : Nat
  next3 : Nat
  next5 : Nat

/-- Advance the ugly number sequence by one step. -/
private def uglyStep (s : UglyState) : UglyState :=
  let nextNum : Nat := min s.next2 (min s.next3 s.next5)
  let arr' : Array Nat := s.arr.push nextNum
  let i2' := if nextNum == s.next2 then s.i2 + 1 else s.i2
  let i3' := if nextNum == s.next3 then s.i3 + 1 else s.i3
  let i5' := if nextNum == s.next5 then s.i5 + 1 else s.i5
  let next2' := if nextNum == s.next2 then arr'.getD i2' 1 * 2 else s.next2
  let next3' := if nextNum == s.next3 then arr'.getD i3' 1 * 3 else s.next3
  let next5' := if nextNum == s.next5 then arr'.getD i5' 1 * 5 else s.next5
  { arr := arr', i2 := i2', i3 := i3', i5 := i5',
    next2 := next2', next3 := next3', next5 := next5' }
-- !benchmark @end global_aux

namespace SpecialNumbers

-- ── API signatures (no markers — fixed vocabulary) ────────────

abbrev UglyNumbersSig := Int → Int

end SpecialNumbers

-- ── Implementation stubs (LLM task) ───────────────────────────

-- !benchmark @start code_aux def=ugly_numbers
-- !benchmark @end code_aux def=ugly_numbers

def SpecialNumbers.ugly_numbers : SpecialNumbers.UglyNumbersSig :=
-- !benchmark @start code def=ugly_numbers
  fun n =>
    -- Python returns ugly_nums[-1] after range(1, n) iterations
    -- For n ≤ 0, range(1, n) is empty, returning ugly_nums[0] = 1
    if n <= 0 then 1
    else
      let steps := (n - 1).toNat
      let init : UglyState := { arr := #[1], i2 := 0, i3 := 0, i5 := 0,
                                  next2 := 2, next3 := 3, next5 := 5 }
      let final := (List.range steps).foldl (fun s _ => uglyStep s) init
      (final.arr.getD (final.arr.size - 1) 1 : Nat)
-- !benchmark @end code def=ugly_numbers
