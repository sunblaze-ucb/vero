import LinkedList.Harness

/-!
# LinkedList.Spec.CircularLinkedList

Specifications for circular linked list operations.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- insertHead conses the element onto the front. -/
def spec_cll_insertHead_cons (impl : RepoImpl) : Prop :=
  ∀ (l : List Int) (a : Int), impl.linkedList.cll_insertHead l a = a :: l

/-- insertTail appends the element to the end. -/
def spec_cll_insertTail_snoc (impl : RepoImpl) : Prop :=
  ∀ (l : List Int) (a : Int), impl.linkedList.cll_insertTail l a = l ++ [a]

/-- insertNth inserts at index n via take/drop split. -/
def spec_cll_insertNth_split (impl : RepoImpl) : Prop :=
  ∀ (l : List Int) (n : Nat) (a : Int),
    impl.linkedList.cll_insertNth l n a = l.take n ++ [a] ++ l.drop n

/-- deleteFront returns none on empty and some (x, xs) on x :: xs. -/
def spec_cll_deleteFront_cases (impl : RepoImpl) : Prop :=
  impl.linkedList.cll_deleteFront [] = none ∧
  ∀ (x : Int) (xs : List Int),
    impl.linkedList.cll_deleteFront (x :: xs) = some (x, xs)

/-- cll_deleteTail returns none on empty and some (a, l) when list ends with a. -/
def spec_cll_deleteTail_cases (impl : RepoImpl) : Prop :=
  impl.linkedList.cll_deleteTail [] = none ∧
  ∀ (l : List Int) (a : Int),
    impl.linkedList.cll_deleteTail (l ++ [a]) = some (a, l)

/-- deleteNth returns none out-of-range and removes the nth element in-range. -/
def spec_cll_deleteNth_cases (impl : RepoImpl) : Prop :=
  (∀ (l : List Int) (n : Nat), n ≥ l.length →
     impl.linkedList.cll_deleteNth l n = none) ∧
  (∀ (before : List Int) (x : Int) (after : List Int),
     impl.linkedList.cll_deleteNth (before ++ [x] ++ after) before.length
       = some (x, before ++ after))

/-- isEmpty agrees with List.isEmpty. -/
def spec_cll_isEmpty_iff_nil (impl : RepoImpl) : Prop :=
  ∀ (l : List Int), impl.linkedList.cll_isEmpty l = l.isEmpty

/-- CLL shared operations agree with their SLL counterparts on every input. -/
def spec_cll_matches_sll (impl : RepoImpl) : Prop :=
  (∀ (l : List Int) (a : Int),
     impl.linkedList.cll_insertHead l a = impl.linkedList.sll_insertHead l a) ∧
  (∀ (l : List Int) (a : Int),
     impl.linkedList.cll_insertTail l a = impl.linkedList.sll_insertTail l a) ∧
  (∀ (l : List Int),
     impl.linkedList.cll_deleteFront l = impl.linkedList.sll_deleteHead l) ∧
  (∀ (l : List Int),
     impl.linkedList.cll_deleteTail l = impl.linkedList.sll_deleteTail l) ∧
  (∀ (l : List Int),
     impl.linkedList.cll_isEmpty l = impl.linkedList.sll_isEmpty l)

/-- PR-#35 EmptyListLaw (CLL): the empty list has length zero and no removable front. -/
def spec_cll_empty_list_law (impl : RepoImpl) : Prop :=
  impl.linkedList.lli_length [] = 0 ∧
  impl.linkedList.cll_deleteFront [] = none

/-- PR-#35 InsertHeadDeleteHeadRoundtrip (CLL): head insertion is undone by deleteFront and grows length. -/
def spec_cll_insertHead_deleteFront_roundtrip (impl : RepoImpl) : Prop :=
  ∀ (l : List Int) (a : Int),
    impl.linkedList.cll_deleteFront (impl.linkedList.cll_insertHead l a) = some (a, l) ∧
    impl.linkedList.lli_length (impl.linkedList.cll_insertHead l a)
      = impl.linkedList.lli_length l + 1

/-- PR-#35 InsertTailDeleteTailRoundtrip (CLL): tail insertion is undone by deleteTail and grows length. -/
def spec_cll_insertTail_deleteTail_roundtrip (impl : RepoImpl) : Prop :=
  ∀ (l : List Int) (a : Int),
    impl.linkedList.cll_deleteTail (impl.linkedList.cll_insertTail l a) = some (a, l) ∧
    impl.linkedList.lli_length (impl.linkedList.cll_insertTail l a)
      = impl.linkedList.lli_length l + 1
