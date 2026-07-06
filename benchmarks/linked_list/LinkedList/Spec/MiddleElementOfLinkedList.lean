import LinkedList.Harness

/-!
# LinkedList.Spec.MiddleElementOfLinkedList

Specifications for middle-element linked list operations.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- push prepends the element, implementing cons. -/
def spec_midll_push_cons (impl : RepoImpl) : Prop :=
  ∀ (l : List Int) (a : Int), impl.linkedList.midll_push l a = a :: l

/-- middleElement is none on empty and element at index length/2 otherwise. -/
def spec_midll_middleElement_cases (impl : RepoImpl) : Prop :=
  impl.linkedList.midll_middleElement [] = none ∧
  ∀ (l : List Int), l ≠ [] →
    impl.linkedList.midll_middleElement l = (l.drop (l.length / 2)).head?

/-- A single-element list has that element as its middle. -/
def spec_midll_middleElement_singleton (impl : RepoImpl) : Prop :=
  ∀ (a : Int), impl.linkedList.midll_middleElement [a] = some a
