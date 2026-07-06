-- !benchmark @start imports
-- !benchmark @end imports

/-!
# LinkedList.Impl.CircularLinkedList

Circular linked list operations modelled as `List α`.

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
Implement only the function bodies.
-/

abbrev CLL.LinkedList (α : Type) := List α

-- !benchmark @start global_aux
-- !benchmark @end global_aux

namespace CLL

variable {α : Type}

abbrev InsertHeadSig  := List α → α → List α
abbrev InsertTailSig  := List α → α → List α
abbrev InsertNthSig   := List α → Nat → α → List α
abbrev DeleteFrontSig := List α → Option (α × List α)
abbrev DeleteTailSig  := List α → Option (α × List α)
abbrev DeleteNthSig   := List α → Nat → Option (α × List α)
abbrev IsEmptySig     := List α → Bool

-- !benchmark @start code_aux def=cll_insertHead
-- !benchmark @end code_aux def=cll_insertHead

def insertHead : List α → α → List α :=
-- !benchmark @start code def=cll_insertHead
  fun l a => a :: l
-- !benchmark @end code def=cll_insertHead

-- !benchmark @start code_aux def=cll_insertTail
-- !benchmark @end code_aux def=cll_insertTail

def insertTail : List α → α → List α :=
-- !benchmark @start code def=cll_insertTail
  fun l a => l ++ [a]
-- !benchmark @end code def=cll_insertTail

-- !benchmark @start code_aux def=cll_insertNth
-- !benchmark @end code_aux def=cll_insertNth

def insertNth : List α → Nat → α → List α :=
-- !benchmark @start code def=cll_insertNth
  fun l n a => l.take n ++ [a] ++ l.drop n
-- !benchmark @end code def=cll_insertNth

-- !benchmark @start code_aux def=cll_deleteFront
-- !benchmark @end code_aux def=cll_deleteFront

def deleteFront : List α → Option (α × List α) :=
-- !benchmark @start code def=cll_deleteFront
  fun l =>
    match l with
    | []      => none
    | x :: xs => some (x, xs)
-- !benchmark @end code def=cll_deleteFront

-- !benchmark @start code_aux def=cll_deleteTail
-- !benchmark @end code_aux def=cll_deleteTail

def deleteTail : List α → Option (α × List α) :=
-- !benchmark @start code def=cll_deleteTail
  fun l =>
    match l.reverse with
    | []      => none
    | x :: xs => some (x, xs.reverse)
-- !benchmark @end code def=cll_deleteTail

-- !benchmark @start code_aux def=cll_deleteNth
-- !benchmark @end code_aux def=cll_deleteNth

def deleteNth : List α → Nat → Option (α × List α) :=
-- !benchmark @start code def=cll_deleteNth
  fun l n =>
    match l.drop n with
    | []     => none
    | x :: _ => some (x, l.take n ++ l.drop (n + 1))
-- !benchmark @end code def=cll_deleteNth

-- !benchmark @start code_aux def=cll_isEmpty
-- !benchmark @end code_aux def=cll_isEmpty

def isEmpty : List α → Bool :=
-- !benchmark @start code def=cll_isEmpty
  fun l => l.isEmpty
-- !benchmark @end code def=cll_isEmpty

end CLL
