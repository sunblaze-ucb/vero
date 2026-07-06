import LinkedList.Harness
import LinkedList.Spec.Aux

/-!
# LinkedList.Spec.MergeTwoLists

Specifications for sorted list merge operations.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- Sorting the empty list produces the empty list. -/
def spec_merge_fromList_empty (impl : RepoImpl) : Prop :=
  impl.linkedList.merge_fromList [] = []

/-- fromList always produces an ascending-sorted list. -/
def spec_merge_fromList_sorted (impl : RepoImpl) : Prop :=
  ∀ (l : List Int),
    spec_helper_isSortedAsc (impl.linkedList.merge_fromList l) = true

/-- fromList preserves exactly the input elements, only reordering them. -/
def spec_merge_fromList_perm (impl : RepoImpl) : Prop :=
  ∀ (l : List Int),
    (impl.linkedList.merge_fromList l).Perm l

/-- Sorting an already-sorted list is a no-op. -/
def spec_merge_fromList_idempotent (impl : RepoImpl) : Prop :=
  ∀ (l : List Int),
    impl.linkedList.merge_fromList (impl.linkedList.merge_fromList l)
      = impl.linkedList.merge_fromList l

/-- Merging the empty list on the left with ys returns ys. -/
def spec_merge_mergeLists_left_id (impl : RepoImpl) : Prop :=
  ∀ (ys : List Int), impl.linkedList.merge_mergeLists [] ys = ys

/-- Merging xs with the empty list returns xs. -/
def spec_merge_mergeLists_right_id (impl : RepoImpl) : Prop :=
  ∀ (xs : List Int), impl.linkedList.merge_mergeLists xs [] = xs

/-- Merging two sorted lists preserves sortedness and combines their lengths. -/
def spec_merge_sorted_preserves_shape (impl : RepoImpl) : Prop :=
  ∀ (xs ys : List Int),
    spec_helper_isSortedAsc xs = true →
    spec_helper_isSortedAsc ys = true →
    spec_helper_isSortedAsc (impl.linkedList.merge_mergeLists xs ys) = true ∧
    (impl.linkedList.merge_mergeLists xs ys).length = xs.length + ys.length

/-- mergeLists preserves exactly the elements of both input lists. -/
def spec_merge_mergeLists_perm_append (impl : RepoImpl) : Prop :=
  ∀ (xs ys : List Int),
    (impl.linkedList.merge_mergeLists xs ys).Perm (xs ++ ys)

/-- The length of the merged list equals the sum of the input lengths. -/
def spec_merge_mergeLists_length (impl : RepoImpl) : Prop :=
  ∀ (xs ys : List Int),
    (impl.linkedList.merge_mergeLists xs ys).length = xs.length + ys.length
