-- !benchmark @start imports
-- !benchmark @end imports

/-!
# LinkedList.Impl.DoublyLinkedList

Doubly-linked list operations modelled as `List α`.

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
Implement only the function bodies.
-/

abbrev DLL.LinkedList (α : Type) := List α

-- !benchmark @start global_aux
-- !benchmark @end global_aux

namespace DLL

variable {α : Type}

abbrev InsertAtHeadSig := List α → α → List α
abbrev InsertAtTailSig := List α → α → List α
abbrev InsertAtNthSig  := List α → Nat → α → List α
abbrev DeleteHeadSig   := List α → Option (α × List α)
abbrev DeleteTailSig   := List α → Option (α × List α)
abbrev DeleteAtNthSig  := List α → Nat → Option (α × List α)
abbrev DeleteDataSig   := [BEq α] → List α → α → Option (α × List α)
abbrev IsEmptySig      := List α → Bool

-- !benchmark @start code_aux def=dll_insertAtHead
-- !benchmark @end code_aux def=dll_insertAtHead

def insertAtHead : List α → α → List α :=
-- !benchmark @start code def=dll_insertAtHead
  fun l a => a :: l
-- !benchmark @end code def=dll_insertAtHead

-- !benchmark @start code_aux def=dll_insertAtTail
-- !benchmark @end code_aux def=dll_insertAtTail

def insertAtTail : List α → α → List α :=
-- !benchmark @start code def=dll_insertAtTail
  fun l a => l ++ [a]
-- !benchmark @end code def=dll_insertAtTail

-- !benchmark @start code_aux def=dll_insertAtNth
-- !benchmark @end code_aux def=dll_insertAtNth

def insertAtNth : List α → Nat → α → List α :=
-- !benchmark @start code def=dll_insertAtNth
  fun l n a => l.take n ++ [a] ++ l.drop n
-- !benchmark @end code def=dll_insertAtNth

-- !benchmark @start code_aux def=dll_deleteHead
-- !benchmark @end code_aux def=dll_deleteHead

def deleteHead : List α → Option (α × List α) :=
-- !benchmark @start code def=dll_deleteHead
  fun l =>
    match l with
    | []      => none
    | x :: xs => some (x, xs)
-- !benchmark @end code def=dll_deleteHead

-- !benchmark @start code_aux def=dll_deleteTail
-- !benchmark @end code_aux def=dll_deleteTail

def deleteTail : List α → Option (α × List α) :=
-- !benchmark @start code def=dll_deleteTail
  fun l =>
    match l.reverse with
    | []      => none
    | x :: xs => some (x, xs.reverse)
-- !benchmark @end code def=dll_deleteTail

-- !benchmark @start code_aux def=dll_deleteAtNth
-- !benchmark @end code_aux def=dll_deleteAtNth

def deleteAtNth : List α → Nat → Option (α × List α) :=
-- !benchmark @start code def=dll_deleteAtNth
  fun l n =>
    match l.drop n with
    | []     => none
    | x :: _ => some (x, l.take n ++ l.drop (n + 1))
-- !benchmark @end code def=dll_deleteAtNth

-- !benchmark @start code_aux def=dll_deleteData
-- Helper: find first occurrence of target and remove it.
private def deleteDataHelper [BEq α] (target : α) : List α → List α → Option (α × List α)
  | _,      []      => none
  | before, x :: xs =>
    if x == target then some (x, before.reverse ++ xs)
    else deleteDataHelper target (x :: before) xs
-- !benchmark @end code_aux def=dll_deleteData

def deleteData [BEq α] : List α → α → Option (α × List α) :=
-- !benchmark @start code def=dll_deleteData
  fun l target => deleteDataHelper target [] l
-- !benchmark @end code def=dll_deleteData

-- !benchmark @start code_aux def=dll_isEmpty
-- !benchmark @end code_aux def=dll_isEmpty

def isEmpty : List α → Bool :=
-- !benchmark @start code def=dll_isEmpty
  fun l => l.isEmpty
-- !benchmark @end code def=dll_isEmpty

end DLL
