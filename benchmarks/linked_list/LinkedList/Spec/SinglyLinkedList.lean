import LinkedList.Harness

/-!
# LinkedList.Spec.SinglyLinkedList

Specifications for singly-linked list operations.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- Inserting at the head conses the element onto the front. -/
def spec_sll_insertHead_cons (impl : RepoImpl) : Prop :=
  ∀ (l : List Int) (a : Int), impl.linkedList.sll_insertHead l a = a :: l

/-- Inserting at the tail appends the element to the end. -/
def spec_sll_insertTail_snoc (impl : RepoImpl) : Prop :=
  ∀ (l : List Int) (a : Int), impl.linkedList.sll_insertTail l a = l ++ [a]

/-- Inserting at index n splits the list at that index. -/
def spec_sll_insertNth_split (impl : RepoImpl) : Prop :=
  ∀ (l : List Int) (n : Nat) (a : Int),
    impl.linkedList.sll_insertNth l n a = l.take n ++ [a] ++ l.drop n

/-- deleteHead returns none on empty and some (x, xs) on x :: xs. -/
def spec_sll_deleteHead_cases (impl : RepoImpl) : Prop :=
  impl.linkedList.sll_deleteHead [] = none ∧
  ∀ (x : Int) (xs : List Int),
    impl.linkedList.sll_deleteHead (x :: xs) = some (x, xs)

/-- deleteTail returns none on empty and some (a, l) when list ends with a. -/
def spec_sll_deleteTail_cases (impl : RepoImpl) : Prop :=
  impl.linkedList.sll_deleteTail [] = none ∧
  ∀ (l : List Int) (a : Int),
    impl.linkedList.sll_deleteTail (l ++ [a]) = some (a, l)

/-- deleteNth returns none out-of-range and removes the nth element in-range. -/
def spec_sll_deleteNth_cases (impl : RepoImpl) : Prop :=
  (∀ (l : List Int) (n : Nat), n ≥ l.length →
     impl.linkedList.sll_deleteNth l n = none) ∧
  (∀ (before : List Int) (x : Int) (after : List Int),
     impl.linkedList.sll_deleteNth (before ++ [x] ++ after) before.length
       = some (x, before ++ after))

/-- isEmpty agrees with List.isEmpty. -/
def spec_sll_isEmpty_iff_nil (impl : RepoImpl) : Prop :=
  ∀ (l : List Int), impl.linkedList.sll_isEmpty l = l.isEmpty

/-- sll_reverse agrees with List.reverse. -/
def spec_sll_reverse_eq_listReverse (impl : RepoImpl) : Prop :=
  ∀ (l : List Int), impl.linkedList.sll_reverse l = l.reverse

/-- Reversing twice yields the original list. -/
def spec_sll_reverse_involutive (impl : RepoImpl) : Prop :=
  ∀ (l : List Int),
    impl.linkedList.sll_reverse (impl.linkedList.sll_reverse l) = l

/-- Head and tail insertion are undone by matching deletion and grow the shared length observer. -/
def spec_sll_insert_delete_roundtrips_and_length (impl : RepoImpl) : Prop :=
  (∀ (l : List Int) (a : Int),
    impl.linkedList.sll_deleteHead (impl.linkedList.sll_insertHead l a) = some (a, l) ∧
    impl.linkedList.lli_length (impl.linkedList.sll_insertHead l a) = impl.linkedList.lli_length l + 1) ∧
  (∀ (l : List Int) (a : Int),
    impl.linkedList.sll_deleteTail (impl.linkedList.sll_insertTail l a) = some (a, l) ∧
    impl.linkedList.lli_length (impl.linkedList.sll_insertTail l a) = impl.linkedList.lli_length l + 1)

/-- PR-#35 EmptyListLaw (SLL): the empty list has length zero and no removable head. -/
def spec_sll_empty_list_law (impl : RepoImpl) : Prop :=
  impl.linkedList.lli_length [] = 0 ∧
  impl.linkedList.sll_deleteHead [] = none
