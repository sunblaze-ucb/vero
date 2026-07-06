import LinkedList.Harness

/-!
# LinkedList.Spec.FromSequence

Specifications for building a linked list from a sequence.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- makeLinkedList returns none for empty and some l for non-empty l. -/
def spec_fromSeq_makeLinkedList_cases (impl : RepoImpl) : Prop :=
  impl.linkedList.fromSeq_makeLinkedList [] = none ∧
  ∀ (l : List Int), l ≠ [] → impl.linkedList.fromSeq_makeLinkedList l = some l
