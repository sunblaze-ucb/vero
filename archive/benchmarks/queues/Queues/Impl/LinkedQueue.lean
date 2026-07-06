-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Queues.Impl.LinkedQueue

FIFO queue backed by a singly-linked list in Python. The Lean
translation uses `List α` (front = head) as the concrete backing
store; `put` appends to the tail, `get` removes from the head,
`clear` returns the empty list.

Types and signatures are fixed vocabulary (DO NOT MODIFY). Function
bodies are the curator's reference implementations.
-/

-- ── Core data types (DO NOT MODIFY) ───────────────────────────────

namespace LinkedQueue

/-- Conceptual linked-list node placeholder.
    The concrete implementation uses `List α` directly.
    @review human: Node is a Python impl detail retained as vocabulary. -/
structure Node (α : Type) where
  data : Option α := none
  deriving Repr, BEq

end LinkedQueue

/-- FIFO queue backed by `List α` (front = head). -/
abbrev LinkedQueue (α : Type) := List α

namespace LinkedQueue

-- ── API signatures (DO NOT MODIFY) ────────────────────────────────

abbrev LengthSig  := ∀ {α : Type}, LinkedQueue α → Nat
abbrev IsEmptySig := ∀ {α : Type}, LinkedQueue α → Bool
abbrev PutSig     := ∀ {α : Type}, LinkedQueue α → α → LinkedQueue α
abbrev GetSig     := ∀ {α : Type}, LinkedQueue α → Option (α × LinkedQueue α)
abbrev ClearSig   := ∀ {α : Type}, LinkedQueue α → LinkedQueue α

end LinkedQueue

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- ── Constructor ────────────────────────────────────────────────────

/-- Build a `LinkedQueue` from a list. -/
def LinkedQueue.fromList {α : Type} (l : List α) : LinkedQueue α := l

-- ── Implementations ────────────────────────────────────────────────

-- !benchmark @start code_aux def=length
-- !benchmark @end code_aux def=length

def LinkedQueue.length : LinkedQueue.LengthSig :=
-- !benchmark @start code def=length
  fun q => List.length q
-- !benchmark @end code def=length

-- !benchmark @start code_aux def=isEmpty
-- !benchmark @end code_aux def=isEmpty

def LinkedQueue.isEmpty : LinkedQueue.IsEmptySig :=
-- !benchmark @start code def=isEmpty
  fun q => List.isEmpty q
-- !benchmark @end code def=isEmpty

-- !benchmark @start code_aux def=put
-- !benchmark @end code_aux def=put

def LinkedQueue.put : LinkedQueue.PutSig :=
-- !benchmark @start code def=put
  fun q a => q ++ [a]
-- !benchmark @end code def=put

-- !benchmark @start code_aux def=get
-- !benchmark @end code_aux def=get

def LinkedQueue.get : LinkedQueue.GetSig :=
-- !benchmark @start code def=get
  fun q =>
    match q with
    | []        => none
    | a :: rest => some (a, rest)
-- !benchmark @end code def=get

-- !benchmark @start code_aux def=clear
-- !benchmark @end code_aux def=clear

def LinkedQueue.clear : LinkedQueue.ClearSig :=
-- !benchmark @start code def=clear
  fun _ => []
-- !benchmark @end code def=clear
