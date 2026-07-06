-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Stack.Impl.Stack

Core data type and operations for a generic stack backed by a `List`.
The stack convention: `push` appends to the end of the list; the head
(first element) is the top. `peek`/`pop` access the head.

`Stack.empty` and `Stack.push` are constructor helpers used by test
cases and the algorithms below; they are not API-bundle entries.

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
Implement only the function bodies.
-/

-- ── Core data type (no markers — fixed vocabulary) ─────────────────

/-- A stack of elements of type `α`, represented as a `List α`.
    The head of the list is the top of the stack. -/
abbrev Stack (α : Type) := List α

namespace Stack

-- ── Constructor helpers (not in Bundle — fixed vocabulary) ─────────

/-- The empty stack. -/
def empty {α : Type} : Stack α := []

/-- Push an element onto the stack.
    Internally appends to the end so that repeated `push` calls followed by
    `fromList` roundtrips are consistent: the last element of the list
    is the first one pushed (the deepest item). -/
def push {α : Type} (x : α) (s : Stack α) : Stack α := s ++ [x]

-- ── API signatures (no markers — fixed vocabulary) ──────────────────

abbrev IsEmptySig  := {α : Type} → Stack α → Bool
abbrev SizeSig     := {α : Type} → Stack α → Nat
abbrev IsFullSig   := {α : Type} → Stack α → Nat → Bool
abbrev PeekSig     := {α : Type} → Stack α → Option α
abbrev PopSig      := {α : Type} → Stack α → Option (α × Stack α)
abbrev ContainsSig := {α : Type} → [BEq α] → α → Stack α → Bool
abbrev FromListSig := {α : Type} → List α → Stack α

end Stack

-- ── Implementation stubs (LLM task) ────────────────────────────────

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- !benchmark @start code_aux def=isEmpty
-- !benchmark @end code_aux def=isEmpty

def Stack.isEmpty : Stack.IsEmptySig :=
-- !benchmark @start code def=isEmpty
  fun s => List.isEmpty s
-- !benchmark @end code def=isEmpty

-- !benchmark @start code_aux def=size
-- !benchmark @end code_aux def=size

def Stack.size : Stack.SizeSig :=
-- !benchmark @start code def=size
  fun s => s.length
-- !benchmark @end code def=size

-- !benchmark @start code_aux def=isFull
-- !benchmark @end code_aux def=isFull

def Stack.isFull : Stack.IsFullSig :=
-- !benchmark @start code def=isFull
  fun s n => s.length >= n
-- !benchmark @end code def=isFull

-- !benchmark @start code_aux def=peek
-- !benchmark @end code_aux def=peek

def Stack.peek : Stack.PeekSig :=
-- !benchmark @start code def=peek
  fun s => s.head?
-- !benchmark @end code def=peek

-- !benchmark @start code_aux def=pop
-- !benchmark @end code_aux def=pop

def Stack.pop : Stack.PopSig :=
-- !benchmark @start code def=pop
  fun s => s.head?.map fun x => (x, s.tail)
-- !benchmark @end code def=pop

-- !benchmark @start code_aux def=contains
-- !benchmark @end code_aux def=contains

def Stack.contains : Stack.ContainsSig :=
-- !benchmark @start code def=contains
  fun x s => s.any (· == x)
-- !benchmark @end code def=contains

-- !benchmark @start code_aux def=fromList
-- !benchmark @end code_aux def=fromList

def Stack.fromList : Stack.FromListSig :=
-- !benchmark @start code def=fromList
  fun l => l.reverse
-- !benchmark @end code def=fromList
