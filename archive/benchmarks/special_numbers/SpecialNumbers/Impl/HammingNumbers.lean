-- !benchmark @start imports
-- !benchmark @end imports

/-!
# SpecialNumbers.Impl.HammingNumbers

Hamming numbers (regular numbers) are of the form 2^i·3^j·5^k.
`hamming n` returns the first n Hamming numbers in ascending order.

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
Implement only the function bodies.
-/

-- !benchmark @start global_aux
private structure HState where
  arr : Array Nat
  i2 : Nat
  i3 : Nat
  i5 : Nat
  n2 : Nat
  n3 : Nat
  n5 : Nat

private def hammingStep (s : HState) : HState :=
  let nextNum := min s.n2 (min s.n3 s.n5)
  let arr := s.arr.push nextNum
  let (i2, n2) :=
    if nextNum == s.n2 then (s.i2 + 1, arr.getD (s.i2 + 1) 1 * 2)
    else (s.i2, s.n2)
  let (i3, n3) :=
    if nextNum == s.n3 then (s.i3 + 1, arr.getD (s.i3 + 1) 1 * 3)
    else (s.i3, s.n3)
  let (i5, n5) :=
    if nextNum == s.n5 then (s.i5 + 1, arr.getD (s.i5 + 1) 1 * 5)
    else (s.i5, s.n5)
  { arr, i2, i3, i5, n2, n3, n5 }
-- !benchmark @end global_aux

namespace SpecialNumbers

-- ── API signatures (no markers — fixed vocabulary) ────────────

abbrev HammingSig := Int → List Nat

end SpecialNumbers

-- ── Implementation stubs (LLM task) ───────────────────────────

-- !benchmark @start code_aux def=hamming
-- !benchmark @end code_aux def=hamming

def SpecialNumbers.hamming : SpecialNumbers.HammingSig :=
-- !benchmark @start code def=hamming
  fun n_element =>
    if n_element < 1 then []
    else
      let count := n_element.toNat
      let init : HState := { arr := #[1], i2 := 0, i3 := 0, i5 := 0, n2 := 2, n3 := 3, n5 := 5 }
      let final := (List.range (count - 1)).foldl (fun s _ => hammingStep s) init
      final.arr.toList
-- !benchmark @end code def=hamming
