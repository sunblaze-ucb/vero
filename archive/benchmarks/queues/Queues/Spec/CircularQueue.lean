import Queues.Harness
import Queues.Spec.Aux

/-!
# Queues.Spec.CircularQueue

Capacity-aware FIFO laws for circular queues.
-/

/-- Newly created circular queues are empty under all non-default observers. -/
def spec_cq_empty_observers (impl : RepoImpl) : Prop :=
  ∀ (capacity : Nat),
    let q : CircularQueue Nat := CircularQueue.newWithCapacity capacity
    impl.queues.cq_size q = 0 ∧
    impl.queues.cq_isEmpty q = true ∧
    impl.queues.cq_dequeue q = none

/-- `size` observes exactly the backing-list length. -/
def spec_cq_size_matches_data_length (impl : RepoImpl) : Prop :=
  ∀ {α : Type} (q : CircularQueue α),
    impl.queues.cq_size q = spec_helper_len q.data

/-- `isEmpty` observes exactly whether the backing list is empty. -/
def spec_cq_isEmpty_matches_data (impl : RepoImpl) : Prop :=
  ∀ {α : Type} (q : CircularQueue α),
    impl.queues.cq_isEmpty q = spec_helper_empty q.data

/-- Enqueueing below capacity appends to the back and increases the observed size. -/
def spec_cq_enqueue_room_appends_and_grows (impl : RepoImpl) : Prop :=
  ∀ {α : Type} (q : CircularQueue α) (x : α),
    spec_helper_len q.data < q.capacity →
      impl.queues.cq_enqueue q x = { q with data := q.data ++ [x] } ∧
      impl.queues.cq_size (impl.queues.cq_enqueue q x) = impl.queues.cq_size q + 1

/-- Enqueueing at or above capacity is a no-op. -/
def spec_cq_enqueue_full_noop (impl : RepoImpl) : Prop :=
  ∀ {α : Type} (q : CircularQueue α) (x : α),
    spec_helper_len q.data ≥ q.capacity →
      impl.queues.cq_enqueue q x = q

/-- On nonempty queues, `first` and `dequeue` agree on the front element. -/
def spec_cq_first_dequeue_agree_on_front (impl : RepoImpl) : Prop :=
  ∀ (capacity : Nat) (x : Nat) (xs : List Nat),
    let q : CircularQueue Nat := { capacity := capacity, data := x :: xs }
    impl.queues.cq_first q = x ∧
    impl.queues.cq_dequeue q = some (x, { q with data := xs })

/-- Enqueueing into an empty positive-capacity queue then dequeueing returns that element. -/
def spec_cq_enqueue_dequeue_empty_roundtrip (impl : RepoImpl) : Prop :=
  ∀ (capacity : Nat) (x : Nat),
    capacity > 0 →
      impl.queues.cq_dequeue
          (impl.queues.cq_enqueue (CircularQueue.newWithCapacity capacity) x) =
        some (x, CircularQueue.newWithCapacity capacity)

-- ── Restored from pre-T1B backup ──────────────────────────────
-- Restored specs for CircularQueue

/-- Enqueueing an element into a non-full queue (capacity 5, one enqueue)
    makes the queue non-empty. -/
def spec_cq_isEmpty_after_enqueue (impl : RepoImpl) : Prop :=
  impl.queues.cq_isEmpty
    (impl.queues.cq_enqueue (CircularQueue.newWithCapacity (α := Nat) 5) 7) = false

/-- After enqueueing a single element into an empty circular queue,
    `first` returns that element. -/
def spec_cq_first_after_enqueue (impl : RepoImpl) : Prop :=
  impl.queues.cq_first
    (impl.queues.cq_enqueue (CircularQueue.newWithCapacity (α := Nat) 3) 42) = 42

/-- When two elements are enqueued in succession, `first` returns the
    earlier-enqueued element (FIFO discipline). -/
def spec_cq_first_FIFO (impl : RepoImpl) : Prop :=
  impl.queues.cq_first
    (impl.queues.cq_enqueue
      (impl.queues.cq_enqueue (CircularQueue.newWithCapacity (α := Nat) 3) 9) 5) = 9

/-- Enqueueing one element into a queue with available capacity increases
    `size` by exactly 1. -/
def spec_cq_enqueue_size_inc (impl : RepoImpl) : Prop :=
  impl.queues.cq_size
    (impl.queues.cq_enqueue (CircularQueue.newWithCapacity (α := Nat) 2) 11) = 1

/-- A capacity-0 queue remains empty even after an enqueue attempt. -/
def spec_cq_enqueue_capacity_zero (impl : RepoImpl) : Prop :=
  impl.queues.cq_isEmpty
    (impl.queues.cq_enqueue (CircularQueue.newWithCapacity (α := Nat) 0) 99) = true

/-- Dequeueing after a single enqueue yields `some` whose first component
    is the enqueued element. -/
def spec_cq_dequeue_after_enqueue (impl : RepoImpl) : Prop :=
  (impl.queues.cq_dequeue
    (impl.queues.cq_enqueue (CircularQueue.newWithCapacity (α := Nat) 5) 7)).map
      (fun p => p.fst) = some 7

/-- With two enqueues (1 then 2), the first dequeue returns 1, confirming FIFO order. -/
def spec_cq_dequeue_fifo (impl : RepoImpl) : Prop :=
  (impl.queues.cq_dequeue
    (impl.queues.cq_enqueue
      (impl.queues.cq_enqueue (CircularQueue.newWithCapacity (α := Nat) 5) 1) 2)).map
        (fun p => p.fst) = some 1
