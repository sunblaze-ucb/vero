-- !benchmark @start imports
-- !benchmark @end imports

/-!
# LinkedList.Impl.DoublyLinkedListTwo

Doubly-linked list variant 2 modelled as `List α`.

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
Implement only the function bodies.
-/

abbrev DLL2.LinkedList (α : Type) := List α

-- !benchmark @start global_aux
-- !benchmark @end global_aux

namespace DLL2

variable {α : Type}

abbrev SetHeadSig          := List α → α → List α
abbrev SetTailSig          := List α → Option α → List α
abbrev InsertSig           := List α → α → List α
abbrev InsertAtPositionSig := List α → Nat → α → List α
abbrev DeleteValueSig      := [DecidableEq α] → List α → α → List α
abbrev IsEmptySig          := List α → Bool
abbrev HeadDataSig         := List α → Option α
abbrev TailDataSig         := List α → Option α

-- !benchmark @start code_aux def=dll2_setHead
-- !benchmark @end code_aux def=dll2_setHead

def setHead : List α → α → List α :=
-- !benchmark @start code def=dll2_setHead
  fun l a =>
    match l with
    | []      => [a]
    | _ :: xs => a :: xs
-- !benchmark @end code def=dll2_setHead

-- !benchmark @start code_aux def=dll2_setTail
-- !benchmark @end code_aux def=dll2_setTail

def setTail : List α → Option α → List α :=
-- !benchmark @start code def=dll2_setTail
  fun l opt =>
    match opt with
    | none   => l.dropLast
    | some a =>
      match l with
      | [] => [a]
      | _  => l.dropLast ++ [a]
-- !benchmark @end code def=dll2_setTail

-- !benchmark @start code_aux def=dll2_insert
-- !benchmark @end code_aux def=dll2_insert

def insert : List α → α → List α :=
-- !benchmark @start code def=dll2_insert
  fun l a => a :: l
-- !benchmark @end code def=dll2_insert

-- !benchmark @start code_aux def=dll2_insertAtPosition
-- !benchmark @end code_aux def=dll2_insertAtPosition

def insertAtPosition : List α → Nat → α → List α :=
-- !benchmark @start code def=dll2_insertAtPosition
  fun l pos a => l.take pos ++ [a] ++ l.drop pos
-- !benchmark @end code def=dll2_insertAtPosition

-- !benchmark @start code_aux def=dll2_deleteValue
-- !benchmark @end code_aux def=dll2_deleteValue

def deleteValue [DecidableEq α] : List α → α → List α :=
-- !benchmark @start code def=dll2_deleteValue
  fun l a => l.filter (· ≠ a)
-- !benchmark @end code def=dll2_deleteValue

-- !benchmark @start code_aux def=dll2_isEmpty
-- !benchmark @end code_aux def=dll2_isEmpty

def isEmpty : List α → Bool :=
-- !benchmark @start code def=dll2_isEmpty
  fun l => l.isEmpty
-- !benchmark @end code def=dll2_isEmpty

-- !benchmark @start code_aux def=dll2_headData
-- !benchmark @end code_aux def=dll2_headData

def headData : List α → Option α :=
-- !benchmark @start code def=dll2_headData
  fun l => l.head?
-- !benchmark @end code def=dll2_headData

-- !benchmark @start code_aux def=dll2_tailData
-- !benchmark @end code_aux def=dll2_tailData

def tailData : List α → Option α :=
-- !benchmark @start code def=dll2_tailData
  fun l => l.getLast?
-- !benchmark @end code def=dll2_tailData

end DLL2
