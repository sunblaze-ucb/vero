-- !benchmark @start imports
-- !benchmark @end imports

/-!
# LinkedList.Impl.SinglyLinkedList

Singly-linked list operations modelled as `List α`.

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
Implement only the function bodies.
-/

abbrev SLL.LinkedList (α : Type) := List α

-- !benchmark @start global_aux
-- !benchmark @end global_aux

namespace SLL

variable {α : Type}

abbrev InsertHeadSig  := List α → α → List α
abbrev InsertTailSig  := List α → α → List α
abbrev InsertNthSig   := List α → Nat → α → List α
abbrev DeleteHeadSig  := List α → Option (α × List α)
abbrev DeleteTailSig  := List α → Option (α × List α)
abbrev DeleteNthSig   := List α → Nat → Option (α × List α)
abbrev IsEmptySig     := List α → Bool
abbrev ReverseSig     := List α → List α

-- !benchmark @start code_aux def=sll_insertHead
-- !benchmark @end code_aux def=sll_insertHead

def insertHead : List α → α → List α :=
-- !benchmark @start code def=sll_insertHead
  fun l a => a :: l
-- !benchmark @end code def=sll_insertHead

-- !benchmark @start code_aux def=sll_insertTail
-- !benchmark @end code_aux def=sll_insertTail

def insertTail : List α → α → List α :=
-- !benchmark @start code def=sll_insertTail
  fun l a => l ++ [a]
-- !benchmark @end code def=sll_insertTail

-- !benchmark @start code_aux def=sll_insertNth
-- !benchmark @end code_aux def=sll_insertNth

def insertNth : List α → Nat → α → List α :=
-- !benchmark @start code def=sll_insertNth
  fun l n a => l.take n ++ [a] ++ l.drop n
-- !benchmark @end code def=sll_insertNth

-- !benchmark @start code_aux def=sll_deleteHead
-- !benchmark @end code_aux def=sll_deleteHead

def deleteHead : List α → Option (α × List α) :=
-- !benchmark @start code def=sll_deleteHead
  fun l =>
    match l with
    | []      => none
    | x :: xs => some (x, xs)
-- !benchmark @end code def=sll_deleteHead

-- !benchmark @start code_aux def=sll_deleteTail
-- !benchmark @end code_aux def=sll_deleteTail

def deleteTail : List α → Option (α × List α) :=
-- !benchmark @start code def=sll_deleteTail
  fun l =>
    match l.reverse with
    | []      => none
    | x :: xs => some (x, xs.reverse)
-- !benchmark @end code def=sll_deleteTail

-- !benchmark @start code_aux def=sll_deleteNth
-- !benchmark @end code_aux def=sll_deleteNth

def deleteNth : List α → Nat → Option (α × List α) :=
-- !benchmark @start code def=sll_deleteNth
  fun l n =>
    match l.drop n with
    | []     => none
    | x :: _ => some (x, l.take n ++ l.drop (n + 1))
-- !benchmark @end code def=sll_deleteNth

-- !benchmark @start code_aux def=sll_isEmpty
-- !benchmark @end code_aux def=sll_isEmpty

def isEmpty : List α → Bool :=
-- !benchmark @start code def=sll_isEmpty
  fun l => l.isEmpty
-- !benchmark @end code def=sll_isEmpty

-- !benchmark @start code_aux def=sll_reverse
-- !benchmark @end code_aux def=sll_reverse

def reverse : List α → List α :=
-- !benchmark @start code def=sll_reverse
  fun l => l.reverse
-- !benchmark @end code def=sll_reverse

end SLL
