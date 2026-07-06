-- !benchmark @start imports
-- !benchmark @end imports

/-!
# LinkedList.Impl.MiddleElementOfLinkedList

Middle-element linked list operations modelled as `List α`.

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
Implement only the function bodies.
-/

abbrev MidLL.LinkedList (α : Type) := List α

-- !benchmark @start global_aux
-- !benchmark @end global_aux

namespace MidLL

variable {α : Type}

abbrev PushSig          := List α → α → List α
abbrev MiddleElementSig := List α → Option α

-- !benchmark @start code_aux def=midll_push
-- !benchmark @end code_aux def=midll_push

def push : List α → α → List α :=
-- !benchmark @start code def=midll_push
  fun l a => a :: l
-- !benchmark @end code def=midll_push

-- !benchmark @start code_aux def=midll_middleElement
-- !benchmark @end code_aux def=midll_middleElement

def middleElement : List α → Option α :=
-- !benchmark @start code def=midll_middleElement
  fun l =>
    if l.isEmpty then none
    else (l.drop (l.length / 2)).head?
-- !benchmark @end code def=midll_middleElement

end MidLL
