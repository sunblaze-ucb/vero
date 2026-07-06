import LinkedList.Harness

/-!
# LinkedList.Spec.DoublyLinkedList

Specifications for doubly-linked list operations.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- insertAtHead conses the element onto the front. -/
def spec_dll_insertAtHead_cons (impl : RepoImpl) : Prop :=
  ∀ (l : List Int) (a : Int), impl.linkedList.dll_insertAtHead l a = a :: l

/-- insertAtTail appends the element to the end. -/
def spec_dll_insertAtTail_snoc (impl : RepoImpl) : Prop :=
  ∀ (l : List Int) (a : Int), impl.linkedList.dll_insertAtTail l a = l ++ [a]

/-- insertAtNth inserts at index n via take/drop split. -/
def spec_dll_insertAtNth_split (impl : RepoImpl) : Prop :=
  ∀ (l : List Int) (n : Nat) (a : Int),
    impl.linkedList.dll_insertAtNth l n a = l.take n ++ [a] ++ l.drop n

/-- deleteHead returns none on empty and some (x, xs) on x :: xs. -/
def spec_dll_deleteHead_cases (impl : RepoImpl) : Prop :=
  impl.linkedList.dll_deleteHead [] = none ∧
  ∀ (x : Int) (xs : List Int),
    impl.linkedList.dll_deleteHead (x :: xs) = some (x, xs)

/-- deleteTail returns none on empty and some (a, l) when list ends with a. -/
def spec_dll_deleteTail_cases (impl : RepoImpl) : Prop :=
  impl.linkedList.dll_deleteTail [] = none ∧
  ∀ (l : List Int) (a : Int),
    impl.linkedList.dll_deleteTail (l ++ [a]) = some (a, l)

/-- deleteAtNth returns none out-of-range and removes the nth element in-range. -/
def spec_dll_deleteAtNth_cases (impl : RepoImpl) : Prop :=
  (∀ (l : List Int) (n : Nat), n ≥ l.length →
     impl.linkedList.dll_deleteAtNth l n = none) ∧
  (∀ (before : List Int) (x : Int) (after : List Int),
     impl.linkedList.dll_deleteAtNth (before ++ [x] ++ after) before.length
       = some (x, before ++ after))

/-- deleteData: absent key → none; present → first occurrence removed. -/
def spec_dll_deleteData_first_match (impl : RepoImpl) : Prop :=
  (∀ (l : List Int) (x : Int), ¬(x ∈ l) →
     impl.linkedList.dll_deleteData l x = none) ∧
  (∀ (before : List Int) (x : Int) (after : List Int),
     ¬(x ∈ before) →
     impl.linkedList.dll_deleteData (before ++ [x] ++ after) x
       = some (x, before ++ after))

/-- isEmpty agrees with List.isEmpty. -/
def spec_dll_isEmpty_iff_nil (impl : RepoImpl) : Prop :=
  ∀ (l : List Int), impl.linkedList.dll_isEmpty l = l.isEmpty

/-- DLL shared operations agree with their SLL counterparts on every input. -/
def spec_dll_matches_sll_on_shared_ops (impl : RepoImpl) : Prop :=
  (∀ (l : List Int) (a : Int),
     impl.linkedList.dll_insertAtHead l a = impl.linkedList.sll_insertHead l a) ∧
  (∀ (l : List Int) (a : Int),
     impl.linkedList.dll_insertAtTail l a = impl.linkedList.sll_insertTail l a) ∧
  (∀ (l : List Int),
     impl.linkedList.dll_deleteHead l = impl.linkedList.sll_deleteHead l) ∧
  (∀ (l : List Int),
     impl.linkedList.dll_deleteTail l = impl.linkedList.sll_deleteTail l) ∧
  (∀ (l : List Int),
     impl.linkedList.dll_isEmpty l = impl.linkedList.sll_isEmpty l)

/-- PR-#35 EmptyListLaw (DLL): the empty list has length zero and no removable head. -/
def spec_dll_empty_list_law (impl : RepoImpl) : Prop :=
  impl.linkedList.lli_length [] = 0 ∧
  impl.linkedList.dll_deleteHead [] = none

/-- PR-#35 InsertHeadDeleteHeadRoundtrip (DLL): head insertion is undone by head deletion and grows length. -/
def spec_dll_insertAtHead_deleteHead_roundtrip (impl : RepoImpl) : Prop :=
  ∀ (l : List Int) (a : Int),
    impl.linkedList.dll_deleteHead (impl.linkedList.dll_insertAtHead l a) = some (a, l) ∧
    impl.linkedList.lli_length (impl.linkedList.dll_insertAtHead l a)
      = impl.linkedList.lli_length l + 1

/-- PR-#35 InsertTailDeleteTailRoundtrip (DLL): tail insertion is undone by tail deletion and grows length. -/
def spec_dll_insertAtTail_deleteTail_roundtrip (impl : RepoImpl) : Prop :=
  ∀ (l : List Int) (a : Int),
    impl.linkedList.dll_deleteTail (impl.linkedList.dll_insertAtTail l a) = some (a, l) ∧
    impl.linkedList.lli_length (impl.linkedList.dll_insertAtTail l a)
      = impl.linkedList.lli_length l + 1
