import Queues.Harness
import Queues.Spec.Aux

/-!
# Queues.Spec.QueueOnPseudoStack

Structural FIFO and rotation laws for the pseudo-stack queue interface.
-/

/-- Empty pseudo-stack queues have zero size and no element to dequeue. -/
def spec_qops_empty_queue_law (impl : RepoImpl) : Prop :=
  impl.queues.qops_size (QueueOnPseudoStack.fromList ([] : List Nat)) = 0 ∧
  impl.queues.qops_get (QueueOnPseudoStack.fromList ([] : List Nat)) = none

/-- Enqueueing any element increases the observed queue size by exactly one. -/
def spec_qops_put_changes_size (impl : RepoImpl) : Prop :=
  ∀ {α : Type} (q : Queue α) (x : α),
    impl.queues.qops_size (impl.queues.qops_put q x) =
      impl.queues.qops_size q + 1

/-- Dequeueing a queue built from a list returns the list head and the tail queue. -/
def spec_qops_get_fromList_preserves_head (impl : RepoImpl) : Prop :=
  ∀ {α : Type} (xs : List α),
    impl.queues.qops_get (QueueOnPseudoStack.fromList xs) =
      match xs with
      | [] => none
      | y :: ys => some (y, QueueOnPseudoStack.fromList ys)

/-- Enqueue after `fromList` appends at the logical back without disturbing the front. -/
def spec_qops_put_after_fromList (impl : RepoImpl) : Prop :=
  ∀ {α : Type} (xs : List α) (x : α),
    impl.queues.qops_get (impl.queues.qops_put (QueueOnPseudoStack.fromList xs) x) =
      match xs with
      | [] => some (x, QueueOnPseudoStack.fromList [])
      | y :: ys => some (y, impl.queues.qops_put (QueueOnPseudoStack.fromList ys) x)

/-- Rotation preserves queue size for every queue and rotation count. -/
def spec_qops_rotate_preserves_size (impl : RepoImpl) : Prop :=
  ∀ {α : Type} (q : Queue α) (n : Nat),
    impl.queues.qops_size (impl.queues.qops_rotate q n) =
      impl.queues.qops_size q

/-- Rotating a queue built from a list exposes the same front as rotating the source list. -/
def spec_qops_rotate_fromList_matches_list_rotation (impl : RepoImpl) : Prop :=
  ∀ {α : Type} (xs : List α) (n : Nat),
    impl.queues.qops_get (impl.queues.qops_rotate (QueueOnPseudoStack.fromList xs) n) =
      match rotateList xs n with
      | [] => none
      | y :: ys => some (y, QueueOnPseudoStack.fromList ys)

/-- `front` agrees with the head of list-built queues, using the default on empty queues. -/
def spec_qops_front_fromList_matches_head (impl : RepoImpl) : Prop :=
  ∀ (xs : List Nat),
    impl.queues.qops_front (QueueOnPseudoStack.fromList xs) =
      match xs with
      | [] => 0
      | y :: _ => y

-- ── Restored from pre-T1B backup ──────────────────────────────
-- Restored specs for QueueOnPseudoStack

/-- A pseudo-stack queue built from 3 elements has size 3. -/
def spec_qops_size_three (impl : RepoImpl) : Prop :=
  impl.queues.qops_size (QueueOnPseudoStack.fromList [10, 20, 30]) = 3

/-- Putting 5 into an empty pseudo-stack queue yields the singleton `[5]`. -/
def spec_qops_put_singleton (impl : RepoImpl) : Prop :=
  impl.queues.qops_put (QueueOnPseudoStack.fromList ([] : List Nat)) 5 =
    QueueOnPseudoStack.fromList [5]

/-- Putting 3 into `[1, 2]` appends to the back, yielding `[1, 2, 3]`. -/
def spec_qops_put_appends (impl : RepoImpl) : Prop :=
  impl.queues.qops_put (QueueOnPseudoStack.fromList [1, 2]) 3 =
    QueueOnPseudoStack.fromList [1, 2, 3]

/-- Putting one element into a 2-element queue increases size to 3. -/
def spec_qops_put_increments_size (impl : RepoImpl) : Prop :=
  impl.queues.qops_size (impl.queues.qops_put (QueueOnPseudoStack.fromList [1, 2]) 3) = 3

/-- Getting from `[10, 20, 30]` returns the head 10 with remainder `[20, 30]`. -/
def spec_qops_get_returns_head (impl : RepoImpl) : Prop :=
  impl.queues.qops_get (QueueOnPseudoStack.fromList [10, 20, 30]) =
    some (10, QueueOnPseudoStack.fromList [20, 30])

/-- Getting from a singleton `[42]` yields `some (42, [])`. -/
def spec_qops_get_singleton (impl : RepoImpl) : Prop :=
  impl.queues.qops_get (QueueOnPseudoStack.fromList [42]) =
    some (42, QueueOnPseudoStack.fromList ([] : List Nat))

/-- Rotating an empty pseudo-stack queue by any amount leaves it empty. -/
def spec_qops_rotate_empty (impl : RepoImpl) : Prop :=
  impl.queues.qops_rotate (QueueOnPseudoStack.fromList ([] : List Nat)) 2 =
    QueueOnPseudoStack.fromList ([] : List Nat)

/-- Rotating `[1, 2, 3]` by 1 moves the first element to the back: `[2, 3, 1]`. -/
def spec_qops_rotate_one (impl : RepoImpl) : Prop :=
  impl.queues.qops_rotate (QueueOnPseudoStack.fromList [1, 2, 3]) 1 =
    QueueOnPseudoStack.fromList [2, 3, 1]

/-- Rotating a 3-element queue by exactly its length is the identity. -/
def spec_qops_rotate_full_is_identity (impl : RepoImpl) : Prop :=
  impl.queues.qops_rotate (QueueOnPseudoStack.fromList [1, 2, 3]) 3 =
    QueueOnPseudoStack.fromList [1, 2, 3]

/-- `front` on an empty pseudo-stack queue returns the default value (0 for `Nat`). -/
def spec_qops_front_empty (impl : RepoImpl) : Prop :=
  impl.queues.qops_front (QueueOnPseudoStack.fromList ([] : List Nat)) = (0 : Nat)

/-- `front` on `[10, 20, 30]` returns the front element 10. -/
def spec_qops_front_returns_head (impl : RepoImpl) : Prop :=
  impl.queues.qops_front (QueueOnPseudoStack.fromList [10, 20, 30]) = 10

