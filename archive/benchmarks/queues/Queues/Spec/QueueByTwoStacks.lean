import Queues.Harness

/-!
# Queues.Spec.QueueByTwoStacks

Structural FIFO laws for the two-stack queue interface.
-/

/-- Empty two-stack queues have zero length and no element to dequeue. -/
def spec_qbts_empty_queue_law (impl : RepoImpl) : Prop :=
  impl.queues.qbts_length (QueueByTwoStacks.fromList ([] : List Nat)) = 0 ∧
  impl.queues.qbts_get (QueueByTwoStacks.fromList ([] : List Nat)) = none

/-- Enqueueing any element increases the observed queue length by exactly one. -/
def spec_qbts_put_changes_length (impl : RepoImpl) : Prop :=
  ∀ {α : Type} (q : QueueByTwoStacks α) (x : α),
    impl.queues.qbts_length (impl.queues.qbts_put q x) =
      impl.queues.qbts_length q + 1

/-- Dequeueing a queue built from a list returns the list head and the tail queue. -/
def spec_qbts_get_fromList_preserves_head (impl : RepoImpl) : Prop :=
  ∀ {α : Type} (xs : List α),
    impl.queues.qbts_get (QueueByTwoStacks.fromList xs) =
      match xs with
      | [] => none
      | y :: ys => some (y, QueueByTwoStacks.fromList ys)

/-- Enqueue after `fromList` appends at the logical back without disturbing the front. -/
def spec_qbts_put_after_fromList (impl : RepoImpl) : Prop :=
  ∀ {α : Type} (xs : List α) (x : α),
    impl.queues.qbts_get (impl.queues.qbts_put (QueueByTwoStacks.fromList xs) x) =
      match xs with
      | [] => some (x, QueueByTwoStacks.fromList [])
      | y :: ys => some (y, impl.queues.qbts_put (QueueByTwoStacks.fromList ys) x)

-- ── Restored from pre-T1B backup ──────────────────────────────
-- Restored specs for QueueByTwoStacks

/-- A two-stack queue built from 3 elements has length 3. -/
def spec_qbts_length_three (impl : RepoImpl) : Prop :=
  impl.queues.qbts_length (QueueByTwoStacks.fromList [10, 20, 30]) = 3

/-- Putting 5 into an empty two-stack queue yields the singleton `[5]`. -/
def spec_qbts_put_singleton (impl : RepoImpl) : Prop :=
  impl.queues.qbts_put (QueueByTwoStacks.fromList ([] : List Nat)) 5 =
    QueueByTwoStacks.fromList [5]

/-- Putting 3 into `[1, 2]` appends to the back, yielding `[1, 2, 3]`. -/
def spec_qbts_put_appends (impl : RepoImpl) : Prop :=
  impl.queues.qbts_put (QueueByTwoStacks.fromList [1, 2]) 3 =
    QueueByTwoStacks.fromList [1, 2, 3]

/-- Putting one element into a 2-element two-stack queue increases length to 3. -/
def spec_qbts_put_increments_length (impl : RepoImpl) : Prop :=
  impl.queues.qbts_length (impl.queues.qbts_put (QueueByTwoStacks.fromList [1, 2]) 3) = 3

/-- Getting from `[10, 20, 30]` returns the head 10 with remainder `[20, 30]`. -/
def spec_qbts_get_returns_head (impl : RepoImpl) : Prop :=
  impl.queues.qbts_get (QueueByTwoStacks.fromList [10, 20, 30]) =
    some (10, QueueByTwoStacks.fromList [20, 30])

/-- Putting 9 into an empty two-stack queue then getting yields `some (9, [])`. -/
def spec_qbts_put_then_get_roundtrip (impl : RepoImpl) : Prop :=
  impl.queues.qbts_get (impl.queues.qbts_put (QueueByTwoStacks.fromList ([] : List Nat)) 9) =
    some (9, QueueByTwoStacks.fromList ([] : List Nat))

