import SequencesV2.Harness

/-!
# SequencesV2.Spec.MergeSort

Frozen specifications for merge-sort operations translated from
`Collections/Sequences/MergeSort.dfy`. Each `spec_*` is a property over an
arbitrary `impl : RepoImpl`.

DO NOT MODIFY - this file is frozen curator-given content.
-/

open SequencesV2

/-- MergeSortBy preserves the multiset and returns a sorted sequence. -/
def spec_Seq_MergeSort_MergeSortBy___ensures_spec (impl : RepoImpl) : Prop :=
  ∀ {T : Type} [DecidableEq T] (a : List T) (lessThanOrEq : T → T → Bool) (h : Relations_TotalOrdering lessThanOrEq), let result := impl.sequences.Seq_MergeSort_MergeSortBy a lessThanOrEq h; Seq_SameMultiset a result ∧ Relations_SortedBy result lessThanOrEq

/-- MergeSortedWith preserves the multiset of both inputs and returns a sorted sequence. -/
def spec_Seq_MergeSort_MergeSortedWith___ensures_spec (impl : RepoImpl) : Prop :=
  ∀ {T : Type} [DecidableEq T] (left right : List T) (lessThanOrEq : T → T → Bool) (hl : Relations_SortedBy left lessThanOrEq) (hr : Relations_SortedBy right lessThanOrEq) (ho : Relations_TotalOrdering lessThanOrEq), let result := impl.sequences.Seq_MergeSort_MergeSortedWith left right lessThanOrEq hl hr ho; Seq_SameMultiset (left ++ right) result ∧ Relations_SortedBy result lessThanOrEq
