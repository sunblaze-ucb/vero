-- !benchmark @start imports
-- !benchmark @end imports

/-!
# SpecialNumbers.Impl.BellNumbers

Bell numbers count the ways to partition a set. B(0)=1, B(1)=1,
B(2)=2, B(3)=5, … computed via the Bell triangle (binomial recurrence).

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
Implement only the function bodies.
-/

-- !benchmark @start global_aux
/-- C(n, k): binomial coefficient.  Returns 1 for k=0 or k=n. -/
private def binomCoeff (n k : Int) : Int :=
  if k == 0 || k == n then 1
  else
    let k := if k > n - k then n - k else k
    (List.range' 0 k.toNat).foldl
      (fun (acc : Int) (i : Nat) => acc * (n - (i : Int)) / ((i : Int) + 1))
      1
-- !benchmark @end global_aux

namespace SpecialNumbers

-- ── API signatures (no markers — fixed vocabulary) ────────────

abbrev BellNumbersSig := Int → List Int

end SpecialNumbers

-- ── Implementation stubs (LLM task) ───────────────────────────

-- !benchmark @start code_aux def=bell_numbers
-- !benchmark @end code_aux def=bell_numbers

def SpecialNumbers.bell_numbers : SpecialNumbers.BellNumbersSig :=
-- !benchmark @start code def=bell_numbers
  fun max_set_length =>
    if max_set_length < 0 then []
    else
      -- bell[i] = Σ_{j=0}^{i-1} C(i-1, j) * bell[j]
      let n := max_set_length.toNat + 1
      -- build the bell array iteratively
      let bell := (List.range n).foldl
        (fun (arr : Array Int) (i : Nat) =>
          if i == 0 then arr.push 1
          else
            let bi := (List.range i).foldl
              (fun (acc : Int) (j : Nat) =>
                acc + binomCoeff (i - 1 : Int) (j : Int) * arr.getD j 0)
              0
            arr.push bi)
        #[]
      bell.toList
-- !benchmark @end code def=bell_numbers
