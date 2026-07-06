import Queues.Harness

/-!
# Queues.Spec.LinkedQueue

Structural FIFO laws for the linked queue interface.
-/

/-- Empty linked queues have zero length, are empty, and cannot be dequeued. -/
def spec_lq_empty_queue_law (impl : RepoImpl) : Prop :=
  impl.queues.lq_length (LinkedQueue.fromList ([] : List Nat)) = 0 ∧
  impl.queues.lq_isEmpty (LinkedQueue.fromList ([] : List Nat)) = true ∧
  impl.queues.lq_get (LinkedQueue.fromList ([] : List Nat)) = none

/-- Enqueueing any element increases the observed queue length by exactly one. -/
def spec_lq_put_changes_length (impl : RepoImpl) : Prop :=
  ∀ {α : Type} (q : LinkedQueue α) (x : α),
    impl.queues.lq_length (impl.queues.lq_put q x) =
      impl.queues.lq_length q + 1

/-- Dequeueing a queue built from a list returns the list head and the tail queue. -/
def spec_lq_get_fromList_preserves_head (impl : RepoImpl) : Prop :=
  ∀ {α : Type} (xs : List α),
    impl.queues.lq_get (LinkedQueue.fromList xs) =
      match xs with
      | [] => none
      | y :: ys => some (y, LinkedQueue.fromList ys)

/-- Enqueue after `fromList` appends at the logical back without disturbing the front. -/
def spec_lq_put_after_fromList (impl : RepoImpl) : Prop :=
  ∀ {α : Type} (xs : List α) (x : α),
    impl.queues.lq_get (impl.queues.lq_put (LinkedQueue.fromList xs) x) =
      match xs with
      | [] => some (x, LinkedQueue.fromList [])
      | y :: ys => some (y, impl.queues.lq_put (LinkedQueue.fromList ys) x)

/-- Clearing any linked queue produces an empty queue under all observers. -/
def spec_lq_clear_empties_queue (impl : RepoImpl) : Prop :=
  ∀ {α : Type} (q : LinkedQueue α),
    impl.queues.lq_length (impl.queues.lq_clear q) = 0 ∧
    impl.queues.lq_isEmpty (impl.queues.lq_clear q) = true ∧
    impl.queues.lq_get (impl.queues.lq_clear q) = none

-- ── Restored from pre-T1B backup ──────────────────────────────
-- Restored specs for LinkedQueue

/-- A linked queue constructed from a 5-element list has length 5. -/
def spec_lq_length_five (impl : RepoImpl) : Prop :=
  impl.queues.lq_length (LinkedQueue.fromList [1, 2, 3, 4, 5]) = 5

/-- A linked queue from a non-empty list is not empty. -/
def spec_lq_isEmpty_nonempty (impl : RepoImpl) : Prop :=
  impl.queues.lq_isEmpty (LinkedQueue.fromList [1, 2, 3]) = false

/-- Putting element 5 into an empty linked queue yields the singleton queue `[5]`. -/
def spec_lq_put_singleton (impl : RepoImpl) : Prop :=
  impl.queues.lq_put (LinkedQueue.fromList ([] : List Nat)) 5 =
    LinkedQueue.fromList [5]

/-- Putting 3 into `[1, 2]` appends to the back, yielding `[1, 2, 3]`. -/
def spec_lq_put_appends (impl : RepoImpl) : Prop :=
  impl.queues.lq_put (LinkedQueue.fromList [1, 2]) 3 =
    LinkedQueue.fromList [1, 2, 3]

/-- Getting from `[1, 2, 3]` returns the head element 1 together with the remainder `[2, 3]`. -/
def spec_lq_get_returns_head (impl : RepoImpl) : Prop :=
  impl.queues.lq_get (LinkedQueue.fromList [1, 2, 3]) =
    some (1, LinkedQueue.fromList [2, 3])

/-- Clearing a 3-element linked queue returns the empty queue. -/
def spec_lq_clear_empties_three (impl : RepoImpl) : Prop :=
  impl.queues.lq_clear (LinkedQueue.fromList [1, 2, 3]) =
    LinkedQueue.fromList ([] : List Nat)

/-- After clearing a non-empty linked queue, `length` returns 0. -/
def spec_lq_clear_length_zero (impl : RepoImpl) : Prop :=
  impl.queues.lq_length (impl.queues.lq_clear (LinkedQueue.fromList [1, 2, 3])) = 0

/-- Putting 9 into an empty queue then getting yields `some (9, [])` — a round-trip
    with no data loss. -/
def spec_lq_put_then_get_roundtrip (impl : RepoImpl) : Prop :=
  impl.queues.lq_get (impl.queues.lq_put (LinkedQueue.fromList ([] : List Nat)) 9) =
    some (9, LinkedQueue.fromList ([] : List Nat))

