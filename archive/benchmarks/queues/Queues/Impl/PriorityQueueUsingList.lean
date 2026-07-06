-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Queues.Impl.PriorityQueueUsingList

Two priority queue variants backed by Python lists.

`FixedPriorityQueue`: three fixed priority levels (0 = highest, 2 =
lowest), each backed by a `List α`. Dequeue returns the front of the
non-empty highest-priority bucket.

`ElementPriorityQueue`: a single unsorted `List α`; dequeue returns
the minimum element (requires `Ord α` and `BEq α`).

Types and signatures are fixed vocabulary (DO NOT MODIFY). Function
bodies are the curator's reference implementations.
-/

-- ── Core data types (DO NOT MODIFY) ───────────────────────────────

/-- Overflow error type (retained as vocabulary; unused in functional impl). -/
abbrev OverFlowError := String

/-- Underflow error type (retained as vocabulary; unused in functional impl). -/
abbrev UnderFlowError := String

/-- Fixed-priority queue with three levels (0 = highest priority). -/
structure FixedPriorityQueue (α : Type) where
  prio0 : List α := []
  prio1 : List α := []
  prio2 : List α := []
  deriving Repr, BEq

/-- Element-priority queue: elements dequeued in ascending order. -/
abbrev ElementPriorityQueue (α : Type) := List α

namespace PriorityQueueUsingList

-- ── API signatures (DO NOT MODIFY) ────────────────────────────────

abbrev FpqEnqueueSig := ∀ {α : Type}, FixedPriorityQueue α → Nat → α → FixedPriorityQueue α
abbrev FpqDequeueSig := ∀ {α : Type}, FixedPriorityQueue α → Option (α × FixedPriorityQueue α)
abbrev EpqEnqueueSig := ∀ {α : Type}, ElementPriorityQueue α → α → ElementPriorityQueue α
/-- `epq_dequeue` requires `Ord α` and `BEq α` to find and remove the minimum.
    @review human: benchmark.json sig has no ordering constraint; added for implementability. -/
abbrev EpqDequeueSig := ∀ {α : Type} [Ord α] [BEq α], ElementPriorityQueue α → Option (α × ElementPriorityQueue α)

end PriorityQueueUsingList

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- ── Constructors ───────────────────────────────────────────────────

/-- Empty `FixedPriorityQueue`. -/
def FixedPriorityQueue.new {α : Type} : FixedPriorityQueue α := {}

/-- Empty `ElementPriorityQueue`. -/
def ElementPriorityQueue.new {α : Type} : ElementPriorityQueue α := []

-- ── Implementations ────────────────────────────────────────────────

-- !benchmark @start code_aux def=fpq_enqueue
-- !benchmark @end code_aux def=fpq_enqueue

def PriorityQueueUsingList.fpq_enqueue : PriorityQueueUsingList.FpqEnqueueSig :=
-- !benchmark @start code def=fpq_enqueue
  fun q priority a =>
    match priority with
    | 0 => { q with prio0 := q.prio0 ++ [a] }
    | 1 => { q with prio1 := q.prio1 ++ [a] }
    | 2 => { q with prio2 := q.prio2 ++ [a] }
    | _ => q  -- invalid priority: no-op
-- !benchmark @end code def=fpq_enqueue

-- !benchmark @start code_aux def=fpq_dequeue
-- !benchmark @end code_aux def=fpq_dequeue

def PriorityQueueUsingList.fpq_dequeue : PriorityQueueUsingList.FpqDequeueSig :=
-- !benchmark @start code def=fpq_dequeue
  fun q =>
    match q.prio0 with
    | a :: rest => some (a, { q with prio0 := rest })
    | [] =>
    match q.prio1 with
    | a :: rest => some (a, { q with prio1 := rest })
    | [] =>
    match q.prio2 with
    | a :: rest => some (a, { q with prio2 := rest })
    | [] => none
-- !benchmark @end code def=fpq_dequeue

-- !benchmark @start code_aux def=epq_enqueue
-- !benchmark @end code_aux def=epq_enqueue

def PriorityQueueUsingList.epq_enqueue : PriorityQueueUsingList.EpqEnqueueSig :=
-- !benchmark @start code def=epq_enqueue
  fun q a => q ++ [a]
-- !benchmark @end code def=epq_enqueue

-- !benchmark @start code_aux def=epq_dequeue
-- !benchmark @end code_aux def=epq_dequeue

-- @review human: Python uses `min(self.queue)` requiring element ordering; added [Ord α] [BEq α].
def PriorityQueueUsingList.epq_dequeue : PriorityQueueUsingList.EpqDequeueSig :=
-- !benchmark @start code def=epq_dequeue
  fun {α} [Ord α] [BEq α] q =>
    match q with
    | [] => none
    | x :: xs =>
      let minVal := xs.foldl (fun acc y => if Ord.compare acc y == .gt then y else acc) x
      some (minVal, q.erase minVal)
-- !benchmark @end code def=epq_dequeue
