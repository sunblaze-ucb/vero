import LinkedList.Harness

/-!
# LinkedList.Spec.DequeDoubly

Specifications for doubly-linked deque operations.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- first returns the head element as Option, agreeing with List.head?. -/
def spec_deque_first_head (impl : RepoImpl) : Prop :=
  ∀ (l : List Int), impl.linkedList.deque_first l = l.head?

/-- last returns the last element as Option, agreeing with List.getLast?. -/
def spec_deque_last_getLast (impl : RepoImpl) : Prop :=
  ∀ (l : List Int), impl.linkedList.deque_last l = l.getLast?

/-- addFirst prepends the element, producing a :: l. -/
def spec_deque_addFirst_cons (impl : RepoImpl) : Prop :=
  ∀ (l : List Int) (a : Int), impl.linkedList.deque_addFirst l a = a :: l

/-- addLast appends the element, producing l ++ [a]. -/
def spec_deque_addLast_snoc (impl : RepoImpl) : Prop :=
  ∀ (l : List Int) (a : Int), impl.linkedList.deque_addLast l a = l ++ [a]

/-- removeFirst returns none on empty and some (x, xs) on x :: xs. -/
def spec_deque_removeFirst_cases (impl : RepoImpl) : Prop :=
  impl.linkedList.deque_removeFirst [] = none ∧
  ∀ (x : Int) (xs : List Int),
    impl.linkedList.deque_removeFirst (x :: xs) = some (x, xs)

/-- removeLast returns none on empty and some (a, l) when list ends with a. -/
def spec_deque_removeLast_cases (impl : RepoImpl) : Prop :=
  impl.linkedList.deque_removeLast [] = none ∧
  ∀ (l : List Int) (a : Int),
    impl.linkedList.deque_removeLast (l ++ [a]) = some (a, l)

/-- isEmpty agrees with List.isEmpty. -/
def spec_deque_isEmpty_iff_nil (impl : RepoImpl) : Prop :=
  ∀ (l : List Int), impl.linkedList.deque_isEmpty l = l.isEmpty

/-- addFirst then first returns some a. -/
def spec_deque_addFirst_first_inverse (impl : RepoImpl) : Prop :=
  ∀ (l : List Int) (a : Int),
    impl.linkedList.deque_first (impl.linkedList.deque_addFirst l a) = some a

/-- addLast then last returns some a. -/
def spec_deque_addLast_last_inverse (impl : RepoImpl) : Prop :=
  ∀ (l : List Int) (a : Int),
    impl.linkedList.deque_last (impl.linkedList.deque_addLast l a) = some a

/-- PR-#35 EmptyListLaw (Deque): empty deque has length zero and no removable first element. -/
def spec_deque_empty_list_law (impl : RepoImpl) : Prop :=
  impl.linkedList.lli_length [] = 0 ∧
  impl.linkedList.deque_removeFirst [] = none
