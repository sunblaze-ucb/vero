import LinkedList.Harness

/-!
# LinkedList.Spec.DoublyLinkedListTwo

Specifications for doubly-linked list (variant 2) operations.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- setHead replaces the head: [] → [a]; (_ :: xs) → a :: xs. -/
def spec_dll2_setHead_replaces_head (impl : RepoImpl) : Prop :=
  (∀ (a : Int), impl.linkedList.dll2_setHead [] a = [a]) ∧
  (∀ (hd : Int) (xs : List Int) (a : Int),
     impl.linkedList.dll2_setHead (hd :: xs) a = a :: xs)

/-- setTail l none drops the last element, equal to l.dropLast. -/
def spec_dll2_setTail_none_dropLast (impl : RepoImpl) : Prop :=
  ∀ (l : List Int), impl.linkedList.dll2_setTail l none = l.dropLast

/-- setTail l (some a) replaces the last element with a: l.dropLast ++ [a]. -/
def spec_dll2_setTail_some_cases (impl : RepoImpl) : Prop :=
  ∀ (l : List Int) (a : Int),
    impl.linkedList.dll2_setTail l (some a) = l.dropLast ++ [a]

/-- dll2_insert prepends the element, implementing cons. -/
def spec_dll2_insert_cons (impl : RepoImpl) : Prop :=
  ∀ (l : List Int) (a : Int), impl.linkedList.dll2_insert l a = a :: l

/-- insertAtPosition inserts at index pos via take/drop split. -/
def spec_dll2_insertAtPosition_split (impl : RepoImpl) : Prop :=
  ∀ (l : List Int) (pos : Nat) (a : Int),
    impl.linkedList.dll2_insertAtPosition l pos a
      = l.take pos ++ [a] ++ l.drop pos

/-- deleteValue removes ALL occurrences of a, equivalent to l.filter (· ≠ a). -/
def spec_dll2_deleteValue_filters_all (impl : RepoImpl) : Prop :=
  ∀ (l : List Int) (a : Int),
    impl.linkedList.dll2_deleteValue l a = l.filter (· ≠ a)

/-- dll2_isEmpty agrees with List.isEmpty. -/
def spec_dll2_isEmpty_iff_nil (impl : RepoImpl) : Prop :=
  ∀ (l : List Int), impl.linkedList.dll2_isEmpty l = l.isEmpty

/-- headData returns the head element wrapped in Option, agreeing with List.head?. -/
def spec_dll2_headData_eq_head (impl : RepoImpl) : Prop :=
  ∀ (l : List Int), impl.linkedList.dll2_headData l = l.head?

/-- tailData returns the last element wrapped in Option, agreeing with List.getLast?. -/
def spec_dll2_tailData_eq_getLast (impl : RepoImpl) : Prop :=
  ∀ (l : List Int), impl.linkedList.dll2_tailData l = l.getLast?
