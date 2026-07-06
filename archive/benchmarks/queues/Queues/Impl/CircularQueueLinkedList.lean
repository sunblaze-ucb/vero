-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Queues.Impl.CircularQueueLinkedList

Circular FIFO queue implemented with a linked-list representation in
Python. The Lean translation uses a capacity-bounded `List α`
(front-to-back) as the concrete backing store, abstracting away the
doubly-linked circular node structure (which has no direct equivalent
in pure Lean).

Types and signatures are fixed vocabulary (DO NOT MODIFY). Function
bodies are the curator's reference implementations.
-/

-- ── Core data types (DO NOT MODIFY) ───────────────────────────────

namespace CircularQueueLinkedList

/-- Conceptual linked-list node placeholder.
    The concrete implementation uses `List α` and does not require Node.
    @review human: Node is a Python impl detail retained as vocabulary. -/
structure Node (α : Type) where
  data : Option α := none
  deriving Repr, BEq

end CircularQueueLinkedList

/-- Circular FIFO queue backed by a capacity-bounded list. -/
structure CircularQueueLinkedList (α : Type) where
  capacity : Nat
  data     : List α   -- front-to-back; invariant: data.length ≤ capacity
  deriving Repr, BEq

namespace CircularQueueLinkedList

-- ── API signatures (DO NOT MODIFY) ────────────────────────────────

abbrev IsEmptySig  := ∀ {α : Type}, CircularQueueLinkedList α → Bool
/-- `first` requires `Inhabited α` to return a default on empty queue. -/
abbrev FirstSig    := ∀ {α : Type} [Inhabited α], CircularQueueLinkedList α → α
abbrev EnqueueSig  := ∀ {α : Type}, CircularQueueLinkedList α → α → CircularQueueLinkedList α
abbrev DequeueSig  := ∀ {α : Type}, CircularQueueLinkedList α → Option (α × CircularQueueLinkedList α)

end CircularQueueLinkedList

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- ── Implementations ────────────────────────────────────────────────

/-- Create a new empty `CircularQueueLinkedList` with the given capacity. -/
def CircularQueueLinkedList.newWithCapacity {α : Type} (n : Nat) : CircularQueueLinkedList α :=
  { capacity := n, data := [] }

-- !benchmark @start code_aux def=isEmpty
-- !benchmark @end code_aux def=isEmpty

def CircularQueueLinkedList.isEmpty : CircularQueueLinkedList.IsEmptySig :=
-- !benchmark @start code def=isEmpty
  fun q => q.data.isEmpty
-- !benchmark @end code def=isEmpty

-- !benchmark @start code_aux def=first
-- !benchmark @end code_aux def=first

-- @review human: Python raises on empty; Lean returns `default` via Inhabited.
def CircularQueueLinkedList.first : CircularQueueLinkedList.FirstSig :=
-- !benchmark @start code def=first
  fun {α} [Inhabited α] q =>
    match q.data with
    | []      => default
    | a :: _ => a
-- !benchmark @end code def=first

-- !benchmark @start code_aux def=enqueue
-- !benchmark @end code_aux def=enqueue

def CircularQueueLinkedList.enqueue : CircularQueueLinkedList.EnqueueSig :=
-- !benchmark @start code def=enqueue
  fun q a =>
    if q.data.length >= q.capacity then q
    else { q with data := q.data ++ [a] }
-- !benchmark @end code def=enqueue

-- !benchmark @start code_aux def=dequeue
-- !benchmark @end code_aux def=dequeue

def CircularQueueLinkedList.dequeue : CircularQueueLinkedList.DequeueSig :=
-- !benchmark @start code def=dequeue
  fun q =>
    match q.data with
    | []        => none
    | a :: rest => some (a, { q with data := rest })
-- !benchmark @end code def=dequeue
