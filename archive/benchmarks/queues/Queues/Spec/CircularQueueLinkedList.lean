import Queues.Harness
import Queues.Spec.Aux

/-!
# Queues.Spec.CircularQueueLinkedList

Capacity-aware FIFO laws for the linked-list circular queue interface.
-/

/-- Newly created linked circular queues are empty under all non-default observers. -/
def spec_cqll_empty_observers (impl : RepoImpl) : Prop :=
  ∀ (capacity : Nat),
    let q : CircularQueueLinkedList Nat := CircularQueueLinkedList.newWithCapacity capacity
    impl.queues.cqll_isEmpty q = true ∧
    impl.queues.cqll_dequeue q = none

/-- `isEmpty` observes exactly whether the backing list is empty. -/
def spec_cqll_isEmpty_matches_data (impl : RepoImpl) : Prop :=
  ∀ {α : Type} (q : CircularQueueLinkedList α),
    impl.queues.cqll_isEmpty q = spec_helper_empty q.data

/-- Enqueueing below capacity appends to the back. -/
def spec_cqll_enqueue_room_appends (impl : RepoImpl) : Prop :=
  ∀ {α : Type} (q : CircularQueueLinkedList α) (x : α),
    spec_helper_len q.data < q.capacity →
      impl.queues.cqll_enqueue q x = { q with data := q.data ++ [x] }

/-- Enqueueing at or above capacity is a no-op. -/
def spec_cqll_enqueue_full_noop (impl : RepoImpl) : Prop :=
  ∀ {α : Type} (q : CircularQueueLinkedList α) (x : α),
    spec_helper_len q.data ≥ q.capacity →
      impl.queues.cqll_enqueue q x = q

/-- On nonempty queues, `first` and `dequeue` agree on the front element. -/
def spec_cqll_first_dequeue_agree_on_front (impl : RepoImpl) : Prop :=
  ∀ (capacity : Nat) (x : Nat) (xs : List Nat),
    let q : CircularQueueLinkedList Nat := { capacity := capacity, data := x :: xs }
    impl.queues.cqll_first q = x ∧
    impl.queues.cqll_dequeue q = some (x, { q with data := xs })

/-- Enqueueing into an empty positive-capacity queue then dequeueing returns that element. -/
def spec_cqll_enqueue_dequeue_empty_roundtrip (impl : RepoImpl) : Prop :=
  ∀ (capacity : Nat) (x : Nat),
    capacity > 0 →
      impl.queues.cqll_dequeue
          (impl.queues.cqll_enqueue (CircularQueueLinkedList.newWithCapacity capacity) x) =
        some (x, CircularQueueLinkedList.newWithCapacity capacity)

-- ── Restored from pre-T1B backup ──────────────────────────────
-- Restored specs for CircularQueueLinkedList

/-- After enqueueing one element into a non-full queue, `isEmpty` returns `false`. -/
def spec_cqll_isEmpty_after_enqueue (impl : RepoImpl) : Prop :=
  impl.queues.cqll_isEmpty
    (impl.queues.cqll_enqueue (CircularQueueLinkedList.newWithCapacity (α := Nat) 6) 1) = false

/-- Calling `first` on an empty linked-list circular queue returns `default` (0 for `Nat`). -/
def spec_cqll_first_empty (impl : RepoImpl) : Prop :=
  impl.queues.cqll_first (CircularQueueLinkedList.newWithCapacity (α := Nat) 4) = (0 : Nat)

/-- After enqueuing element 17 into an empty queue, `first` returns 17. -/
def spec_cqll_first_after_enqueue (impl : RepoImpl) : Prop :=
  impl.queues.cqll_first
    (impl.queues.cqll_enqueue (CircularQueueLinkedList.newWithCapacity (α := Nat) 4) 17) = 17

/-- Enqueueing element 21 and immediately dequeueing returns `some 21` as the element. -/
def spec_cqll_enqueue_dequeue_roundtrip (impl : RepoImpl) : Prop :=
  (impl.queues.cqll_dequeue
    (impl.queues.cqll_enqueue (CircularQueueLinkedList.newWithCapacity (α := Nat) 3) 21)).map
      (fun p => p.fst) = some 21

/-- Enqueueing 1 then 2 and then dequeueing yields 1 — FIFO discipline. -/
def spec_cqll_dequeue_fifo (impl : RepoImpl) : Prop :=
  (impl.queues.cqll_dequeue
    (impl.queues.cqll_enqueue
      (impl.queues.cqll_enqueue (CircularQueueLinkedList.newWithCapacity (α := Nat) 6) 1) 2)).map
        (fun p => p.fst) = some 1
