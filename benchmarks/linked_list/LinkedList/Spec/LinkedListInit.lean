import LinkedList.Harness

/-!
# LinkedList.Spec.LinkedListInit

Specifications for position-based linked list init operations.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- lli_add inserts item at position via take/drop split. -/
def spec_lli_add_split (impl : RepoImpl) : Prop :=
  ∀ (l : List Int) (item : Int) (position : Nat),
    impl.linkedList.lli_add l item position
      = l.take position ++ [item] ++ l.drop position

/-- lli_remove is head-removal: none on empty, some (x, xs) on x :: xs. -/
def spec_lli_remove_cases (impl : RepoImpl) : Prop :=
  impl.linkedList.lli_remove [] = none ∧
  ∀ (x : Int) (xs : List Int),
    impl.linkedList.lli_remove (x :: xs) = some (x, xs)

/-- lli_isEmpty agrees with List.isEmpty. -/
def spec_lli_isEmpty_iff_nil (impl : RepoImpl) : Prop :=
  ∀ (l : List Int), impl.linkedList.lli_isEmpty l = l.isEmpty

/-- lli_length agrees with List.length. -/
def spec_lli_length_eq_listLength (impl : RepoImpl) : Prop :=
  ∀ (l : List Int), impl.linkedList.lli_length l = l.length

/-- Adding an element at any position increases the length by exactly 1. -/
def spec_lli_add_increases_length (impl : RepoImpl) : Prop :=
  ∀ (l : List Int) (item : Int) (position : Nat),
    impl.linkedList.lli_length (impl.linkedList.lli_add l item position)
      = impl.linkedList.lli_length l + 1
