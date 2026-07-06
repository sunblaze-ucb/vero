import LinkedList.Harness

/-!
# LinkedList.Spec.PrintReverse

Specifications for print-reverse linked list operations.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- printrev_makeLinkedList is the identity function on List Int. -/
def spec_printrev_makeLinkedList_id (impl : RepoImpl) : Prop :=
  ∀ (l : List Int), impl.linkedList.printrev_makeLinkedList l = l

/-- inReverse returns the elements in reverse order, equal to List.reverse. -/
def spec_printrev_inReverse_eq_reverse (impl : RepoImpl) : Prop :=
  ∀ (l : List Int), impl.linkedList.printrev_inReverse l = l.reverse

/-- Reversing twice yields the original list. -/
def spec_printrev_inReverse_involutive (impl : RepoImpl) : Prop :=
  ∀ (l : List Int),
    impl.linkedList.printrev_inReverse (impl.linkedList.printrev_inReverse l) = l
