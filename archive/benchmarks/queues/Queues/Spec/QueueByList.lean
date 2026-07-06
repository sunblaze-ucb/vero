import Queues.Harness
import Queues.Spec.Aux

/-!
# Queues.Spec.QueueByList

Structural FIFO laws for the list-backed queue interface.
-/

/-- Empty list-backed queues have zero length and no element to dequeue. -/
def spec_qbl_empty_queue_law (impl : RepoImpl) : Prop :=
  impl.queues.qbl_length (QueueByList.fromList ([] : List Nat)) = 0 ∧
  impl.queues.qbl_get (QueueByList.fromList ([] : List Nat)) = none

/-- Enqueueing any element increases the observed queue length by exactly one. -/
def spec_qbl_put_changes_length (impl : RepoImpl) : Prop :=
  ∀ {α : Type} (q : QueueByList α) (x : α),
    impl.queues.qbl_length (impl.queues.qbl_put q x) =
      impl.queues.qbl_length q + 1

/-- Dequeueing a queue built from a list returns the list head and the tail queue. -/
def spec_qbl_get_fromList_preserves_head (impl : RepoImpl) : Prop :=
  ∀ {α : Type} (xs : List α),
    impl.queues.qbl_get (QueueByList.fromList xs) =
      match xs with
      | [] => none
      | y :: ys => some (y, QueueByList.fromList ys)

/-- Enqueue after `fromList` appends at the logical back without disturbing the front. -/
def spec_qbl_put_after_fromList (impl : RepoImpl) : Prop :=
  ∀ {α : Type} (xs : List α) (x : α),
    impl.queues.qbl_get (impl.queues.qbl_put (QueueByList.fromList xs) x) =
      match xs with
      | [] => some (x, QueueByList.fromList [])
      | y :: ys => some (y, impl.queues.qbl_put (QueueByList.fromList ys) x)

/-- Rotation preserves queue length for every queue and rotation count. -/
def spec_qbl_rotate_preserves_length (impl : RepoImpl) : Prop :=
  ∀ {α : Type} (q : QueueByList α) (n : Nat),
    impl.queues.qbl_length (impl.queues.qbl_rotate q n) =
      impl.queues.qbl_length q

/-- Rotating a queue built from a list exposes the same front as rotating the source list. -/
def spec_qbl_rotate_fromList_matches_list_rotation (impl : RepoImpl) : Prop :=
  ∀ {α : Type} (xs : List α) (n : Nat),
    impl.queues.qbl_get (impl.queues.qbl_rotate (QueueByList.fromList xs) n) =
      match rotateList xs n with
      | [] => none
      | y :: ys => some (y, QueueByList.fromList ys)

/-- `getFront` agrees with the front element observed through `get` on list-built queues. -/
def spec_qbl_getFront_fromList_matches_head (impl : RepoImpl) : Prop :=
  ∀ (xs : List Nat),
    impl.queues.qbl_getFront (QueueByList.fromList xs) =
      match xs with
      | [] => 0
      | y :: _ => y

-- ── Restored from pre-T1B backup ──────────────────────────────
-- Restored specs for QueueByList

/-- A list-backed queue from 3 elements has length 3. -/
def spec_qbl_length_three (impl : RepoImpl) : Prop :=
  impl.queues.qbl_length (QueueByList.fromList [10, 20, 30]) = 3

/-- Putting 5 into an empty queue yields the singleton `[5]`. -/
def spec_qbl_put_singleton (impl : RepoImpl) : Prop :=
  impl.queues.qbl_put (QueueByList.fromList ([] : List Nat)) 5 =
    QueueByList.fromList [5]

/-- Putting 3 into `[1, 2]` appends to the back: result is `[1, 2, 3]`. -/
def spec_qbl_put_appends (impl : RepoImpl) : Prop :=
  impl.queues.qbl_put (QueueByList.fromList [1, 2]) 3 =
    QueueByList.fromList [1, 2, 3]

/-- Putting one element into a 2-element queue increases length to 3. -/
def spec_qbl_put_increments_length (impl : RepoImpl) : Prop :=
  impl.queues.qbl_length (impl.queues.qbl_put (QueueByList.fromList [1, 2]) 3) = 3

/-- Getting from `[10, 20, 30]` returns the front element 10 with remainder `[20, 30]`. -/
def spec_qbl_get_returns_head (impl : RepoImpl) : Prop :=
  impl.queues.qbl_get (QueueByList.fromList [10, 20, 30]) =
    some (10, QueueByList.fromList [20, 30])

/-- Getting from a singleton queue `[42]` yields `some (42, [])`. -/
def spec_qbl_get_singleton (impl : RepoImpl) : Prop :=
  impl.queues.qbl_get (QueueByList.fromList [42]) =
    some (42, QueueByList.fromList ([] : List Nat))

/-- Rotating an empty queue by any amount leaves it empty. -/
def spec_qbl_rotate_empty (impl : RepoImpl) : Prop :=
  impl.queues.qbl_rotate (QueueByList.fromList ([] : List Nat)) 3 =
    QueueByList.fromList ([] : List Nat)

/-- Rotating `[1, 2, 3]` by 1 moves the front element to the back, yielding `[2, 3, 1]`. -/
def spec_qbl_rotate_one (impl : RepoImpl) : Prop :=
  impl.queues.qbl_rotate (QueueByList.fromList [1, 2, 3]) 1 =
    QueueByList.fromList [2, 3, 1]

/-- Rotating a 3-element queue by exactly its length is the identity. -/
def spec_qbl_rotate_full_is_identity (impl : RepoImpl) : Prop :=
  impl.queues.qbl_rotate (QueueByList.fromList [1, 2, 3]) 3 =
    QueueByList.fromList [1, 2, 3]

/-- `getFront` on an empty queue returns the default value (0 for `Nat`). -/
def spec_qbl_getFront_empty (impl : RepoImpl) : Prop :=
  impl.queues.qbl_getFront (QueueByList.fromList ([] : List Nat)) = (0 : Nat)

/-- `getFront` on `[10, 20, 30]` returns the front element 10. -/
def spec_qbl_getFront_returns_head (impl : RepoImpl) : Prop :=
  impl.queues.qbl_getFront (QueueByList.fromList [10, 20, 30]) = 10

