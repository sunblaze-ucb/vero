-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Queues.Impl.CircularQueue

Circular FIFO queue with a fixed capacity, implemented as a structure
wrapping a bounded `List α` (front-to-back). Enqueue appends to the
back; dequeue removes from the front. When the queue is full, enqueue
is a no-op (mirrors the Python `raise Exception("QUEUE IS FULL")`
path, translated to a safe total function).

Types and signatures are fixed vocabulary (DO NOT MODIFY). Function
bodies are the curator's reference implementations.
-/

-- ── Core data type (DO NOT MODIFY) ────────────────────────────────

/-- Circular FIFO queue with a fixed capacity.
    Internally backed by a list of at most `capacity` elements. -/
structure CircularQueue (α : Type) where
  capacity : Nat
  data     : List α   -- front-to-back; invariant: data.length ≤ capacity
  deriving Repr, BEq

namespace CircularQueue

-- ── API signatures (DO NOT MODIFY) ────────────────────────────────

abbrev SizeSig     := ∀ {α : Type}, CircularQueue α → Nat
abbrev IsEmptySig  := ∀ {α : Type}, CircularQueue α → Bool
/-- `first` requires `Inhabited α` to provide a default on empty queue
    (Python returns `False` on empty; Lean returns `default`). -/
abbrev FirstSig    := ∀ {α : Type} [Inhabited α], CircularQueue α → α
abbrev EnqueueSig  := ∀ {α : Type}, CircularQueue α → α → CircularQueue α
abbrev DequeueSig  := ∀ {α : Type}, CircularQueue α → Option (α × CircularQueue α)

end CircularQueue

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- ── Implementations ────────────────────────────────────────────────

/-- Create a new empty `CircularQueue` with the given capacity. -/
def CircularQueue.newWithCapacity {α : Type} (n : Nat) : CircularQueue α :=
  { capacity := n, data := [] }

-- !benchmark @start code_aux def=size
-- !benchmark @end code_aux def=size

def CircularQueue.size : CircularQueue.SizeSig :=
-- !benchmark @start code def=size
  fun q => q.data.length
-- !benchmark @end code def=size

-- !benchmark @start code_aux def=isEmpty
-- !benchmark @end code_aux def=isEmpty

def CircularQueue.isEmpty : CircularQueue.IsEmptySig :=
-- !benchmark @start code def=isEmpty
  fun q => q.data.isEmpty
-- !benchmark @end code def=isEmpty

-- !benchmark @start code_aux def=first
-- !benchmark @end code_aux def=first

-- @review human: Python returns `False` on empty queue; Lean returns `default` via Inhabited.
def CircularQueue.first : CircularQueue.FirstSig :=
-- !benchmark @start code def=first
  fun {α} [Inhabited α] q =>
    match q.data with
    | []      => default
    | a :: _ => a
-- !benchmark @end code def=first

-- !benchmark @start code_aux def=enqueue
-- !benchmark @end code_aux def=enqueue

def CircularQueue.enqueue : CircularQueue.EnqueueSig :=
-- !benchmark @start code def=enqueue
  fun q a =>
    if q.data.length >= q.capacity then q
    else { q with data := q.data ++ [a] }
-- !benchmark @end code def=enqueue

-- !benchmark @start code_aux def=dequeue
-- !benchmark @end code_aux def=dequeue

def CircularQueue.dequeue : CircularQueue.DequeueSig :=
-- !benchmark @start code def=dequeue
  fun q =>
    match q.data with
    | []        => none
    | a :: rest => some (a, { q with data := rest })
-- !benchmark @end code def=dequeue
