-- !benchmark @start imports
-- !benchmark @end imports

/-!
# LinkedList.Impl.DequeDoubly

Doubly-linked deque operations modelled as `List α`.

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
Implement only the function bodies.
-/

abbrev Deque.LinkedDeque (α : Type) := List α

-- !benchmark @start global_aux
-- !benchmark @end global_aux

namespace Deque

variable {α : Type}

abbrev FirstSig       := List α → Option α
abbrev LastSig        := List α → Option α
abbrev AddFirstSig    := List α → α → List α
abbrev AddLastSig     := List α → α → List α
abbrev RemoveFirstSig := List α → Option (α × List α)
abbrev RemoveLastSig  := List α → Option (α × List α)
abbrev IsEmptySig     := List α → Bool

-- !benchmark @start code_aux def=deque_first
-- !benchmark @end code_aux def=deque_first

def first : List α → Option α :=
-- !benchmark @start code def=deque_first
  fun d => d.head?
-- !benchmark @end code def=deque_first

-- !benchmark @start code_aux def=deque_last
-- !benchmark @end code_aux def=deque_last

def last : List α → Option α :=
-- !benchmark @start code def=deque_last
  fun d => d.getLast?
-- !benchmark @end code def=deque_last

-- !benchmark @start code_aux def=deque_addFirst
-- !benchmark @end code_aux def=deque_addFirst

def addFirst : List α → α → List α :=
-- !benchmark @start code def=deque_addFirst
  fun d a => a :: d
-- !benchmark @end code def=deque_addFirst

-- !benchmark @start code_aux def=deque_addLast
-- !benchmark @end code_aux def=deque_addLast

def addLast : List α → α → List α :=
-- !benchmark @start code def=deque_addLast
  fun d a => d ++ [a]
-- !benchmark @end code def=deque_addLast

-- !benchmark @start code_aux def=deque_removeFirst
-- !benchmark @end code_aux def=deque_removeFirst

def removeFirst : List α → Option (α × List α) :=
-- !benchmark @start code def=deque_removeFirst
  fun d =>
    match d with
    | []      => none
    | x :: xs => some (x, xs)
-- !benchmark @end code def=deque_removeFirst

-- !benchmark @start code_aux def=deque_removeLast
-- !benchmark @end code_aux def=deque_removeLast

def removeLast : List α → Option (α × List α) :=
-- !benchmark @start code def=deque_removeLast
  fun d =>
    match d.reverse with
    | []      => none
    | x :: xs => some (x, xs.reverse)
-- !benchmark @end code def=deque_removeLast

-- !benchmark @start code_aux def=deque_isEmpty
-- !benchmark @end code_aux def=deque_isEmpty

def isEmpty : List α → Bool :=
-- !benchmark @start code def=deque_isEmpty
  fun d => d.isEmpty
-- !benchmark @end code def=deque_isEmpty

end Deque
