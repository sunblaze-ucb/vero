import SequencesV2.Impl.Seq
import SequencesV2.Impl.Trusted

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# SequencesV2.Impl.MergeSort

Merge-sort operations translated from `Collections/Sequences/MergeSort.dfy`.
Types and signatures are fixed vocabulary (DO NOT MODIFY). Function bodies are
the curator's reference implementations inside the `code` markers.
-/

namespace SequencesV2

-- API signatures

abbrev Seq_MergeSort_MergeSortBySig :=
  {T : Type} → (a : List T) → (lessThanOrEq : T → T → Bool) →
    Relations_TotalOrdering lessThanOrEq → List T

abbrev Seq_MergeSort_MergeSortedWithSig :=
  {T : Type} → (left right : List T) → (lessThanOrEq : T → T → Bool) →
    Relations_SortedBy left lessThanOrEq → Relations_SortedBy right lessThanOrEq →
    Relations_TotalOrdering lessThanOrEq → List T

end SequencesV2

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- !benchmark @start code_aux def=Seq_MergeSort_MergeSortBy
-- !benchmark @end code_aux def=Seq_MergeSort_MergeSortBy

def SequencesV2.Seq_MergeSort_MergeSortBy : SequencesV2.Seq_MergeSort_MergeSortBySig :=
-- !benchmark @start code def=Seq_MergeSort_MergeSortBy
  fun {T} a lessThanOrEq _h =>
    let rec mergeFuel : Nat → List T → List T → List T
      | 0, left, right => left ++ right
      | _fuel + 1, [], right => right
      | _fuel + 1, left, [] => left
      | fuel + 1, x :: xs, y :: ys =>
          if lessThanOrEq x y then
            x :: mergeFuel fuel xs (y :: ys)
          else
            y :: mergeFuel fuel (x :: xs) ys
    let rec sortFuel : Nat → List T → List T
      | 0, xs => xs
      | _fuel + 1, [] => []
      | _fuel + 1, [x] => [x]
      | fuel + 1, xs =>
          let splitIndex := xs.length / 2
          let left := xs.take splitIndex
          let right := xs.drop splitIndex
          mergeFuel xs.length (sortFuel fuel left) (sortFuel fuel right)
    sortFuel a.length a
-- !benchmark @end code def=Seq_MergeSort_MergeSortBy

-- !benchmark @start code_aux def=Seq_MergeSort_MergeSortedWith
-- !benchmark @end code_aux def=Seq_MergeSort_MergeSortedWith

def SequencesV2.Seq_MergeSort_MergeSortedWith : SequencesV2.Seq_MergeSort_MergeSortedWithSig :=
-- !benchmark @start code def=Seq_MergeSort_MergeSortedWith
  fun {T} left right lessThanOrEq _hl _hr _ho =>
    let rec mergeFuel : Nat → List T → List T → List T
      | 0, left, right => left ++ right
      | _fuel + 1, [], right => right
      | _fuel + 1, left, [] => left
      | fuel + 1, x :: xs, y :: ys =>
          if lessThanOrEq x y then
            x :: mergeFuel fuel xs (y :: ys)
          else
            y :: mergeFuel fuel (x :: xs) ys
    mergeFuel (left.length + right.length) left right
-- !benchmark @end code def=Seq_MergeSort_MergeSortedWith
