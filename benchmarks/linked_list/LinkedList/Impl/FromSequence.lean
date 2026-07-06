-- !benchmark @start imports
-- !benchmark @end imports

/-!
# LinkedList.Impl.FromSequence

Build a linked list from a sequence. Returns `none` for empty input.

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
Implement only the function bodies.
-/

abbrev FromSeq.Node (α : Type) := List α

-- !benchmark @start global_aux
-- !benchmark @end global_aux

namespace FromSeq

variable {α : Type}

abbrev MakeLinkedListSig := List α → Option (List α)

-- !benchmark @start code_aux def=fromSeq_makeLinkedList
-- !benchmark @end code_aux def=fromSeq_makeLinkedList

def makeLinkedList : List α → Option (List α) :=
-- !benchmark @start code def=fromSeq_makeLinkedList
  fun elements =>
    if elements.isEmpty then none else some elements
-- !benchmark @end code def=fromSeq_makeLinkedList

end FromSeq
