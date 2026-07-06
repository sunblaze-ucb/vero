import Queues.Harness
import Queues.Spec.Aux

/-!
# Queues.Spec.DoubleEndedQueue

Cross-endpoint laws for the double-ended queue interface.
-/

/-- Empty deques have zero length, are empty, and neither endpoint can be popped. -/
def spec_deque_empty_observers (impl : RepoImpl) : Prop :=
  impl.queues.deque_length (DoubleEndedQueue.fromList ([] : List Nat)) = 0 ∧
  impl.queues.deque_isEmpty (DoubleEndedQueue.fromList ([] : List Nat)) = true ∧
  impl.queues.deque_pop (DoubleEndedQueue.fromList ([] : List Nat)) = none ∧
  impl.queues.deque_popLeft (DoubleEndedQueue.fromList ([] : List Nat)) = none

/-- Basic observers agree with the functional list representation. -/
def spec_deque_observers_match_list (impl : RepoImpl) : Prop :=
  ∀ {α : Type} (d : Deque α),
    impl.queues.deque_length d = spec_helper_len d ∧
    impl.queues.deque_isEmpty d = spec_helper_empty d

/-- Appending on the right increases length and is undone by popping from the right. -/
def spec_deque_append_pop_roundtrip (impl : RepoImpl) : Prop :=
  ∀ {α : Type} (d : Deque α) (x : α),
    impl.queues.deque_length (impl.queues.deque_append d x) =
      impl.queues.deque_length d + 1 ∧
    impl.queues.deque_pop (impl.queues.deque_append d x) = some (x, d)

/-- Appending on the left increases length and is undone by popping from the left. -/
def spec_deque_appendLeft_popLeft_roundtrip (impl : RepoImpl) : Prop :=
  ∀ {α : Type} (d : Deque α) (x : α),
    impl.queues.deque_length (impl.queues.deque_appendLeft d x) =
      impl.queues.deque_length d + 1 ∧
    impl.queues.deque_popLeft (impl.queues.deque_appendLeft d x) = some (x, d)

/-- `extend` is the same as repeatedly appending the supplied elements on the right. -/
def spec_deque_extend_matches_repeated_append (impl : RepoImpl) : Prop :=
  ∀ {α : Type} (d : Deque α) (xs : List α),
    impl.queues.deque_extend d xs =
      xs.foldl (fun acc x => impl.queues.deque_append acc x) d

/-- `extendLeft` is the same as repeatedly appending the supplied elements on the left. -/
def spec_deque_extendLeft_matches_repeated_appendLeft (impl : RepoImpl) : Prop :=
  ∀ {α : Type} (d : Deque α) (xs : List α),
    impl.queues.deque_extendLeft d xs =
      xs.foldl (fun acc x => impl.queues.deque_appendLeft acc x) d

-- ── Restored from pre-T1B backup ──────────────────────────────
-- Restored specs for DoubleEndedQueue

/-- A deque constructed from a non-empty list is not empty. -/
def spec_deque_isEmpty_nonempty (impl : RepoImpl) : Prop :=
  impl.queues.deque_isEmpty (DoubleEndedQueue.fromList [1, 2, 3]) = false

/-- The length of a deque constructed from a 3-element list is 3. -/
def spec_deque_length_three (impl : RepoImpl) : Prop :=
  impl.queues.deque_length (DoubleEndedQueue.fromList [1, 2, 3]) = 3

/-- Appending element 5 to an empty deque produces the singleton deque `[5]`. -/
def spec_deque_append_singleton (impl : RepoImpl) : Prop :=
  impl.queues.deque_append (DoubleEndedQueue.fromList ([] : List Nat)) 5 =
    DoubleEndedQueue.fromList [5]

/-- Appending 3 to `[1, 2]` yields `[1, 2, 3]` -- the element lands at the right end. -/
def spec_deque_append_appends (impl : RepoImpl) : Prop :=
  impl.queues.deque_append (DoubleEndedQueue.fromList [1, 2]) 3 =
    DoubleEndedQueue.fromList [1, 2, 3]

/-- Prepending element 5 to an empty deque produces the singleton `[5]`. -/
def spec_deque_appendLeft_singleton (impl : RepoImpl) : Prop :=
  impl.queues.deque_appendLeft (DoubleEndedQueue.fromList ([] : List Nat)) 5 =
    DoubleEndedQueue.fromList [5]

/-- Prepending 1 to `[2, 3]` yields `[1, 2, 3]` -- the element lands at the left end. -/
def spec_deque_appendLeft_prepends (impl : RepoImpl) : Prop :=
  impl.queues.deque_appendLeft (DoubleEndedQueue.fromList [2, 3]) 1 =
    DoubleEndedQueue.fromList [1, 2, 3]

/-- Extending a deque with an empty list leaves it unchanged. -/
def spec_deque_extend_empty (impl : RepoImpl) : Prop :=
  impl.queues.deque_extend (DoubleEndedQueue.fromList [1, 2]) ([] : List Nat) =
    DoubleEndedQueue.fromList [1, 2]

/-- Extending `[1, 2]` with `[3, 4]` appends in order to produce `[1, 2, 3, 4]`. -/
def spec_deque_extend_appends_list (impl : RepoImpl) : Prop :=
  impl.queues.deque_extend (DoubleEndedQueue.fromList [1, 2]) [3, 4] =
    DoubleEndedQueue.fromList [1, 2, 3, 4]

/-- Extending a deque on the left with an empty list leaves it unchanged. -/
def spec_deque_extendLeft_empty (impl : RepoImpl) : Prop :=
  impl.queues.deque_extendLeft (DoubleEndedQueue.fromList [1, 2]) ([] : List Nat) =
    DoubleEndedQueue.fromList [1, 2]

/-- Python extendleft prepends elements one-by-one (reversing the iterable).
    Extending `[1,2,3]` from the left with `[0, 5]` yields `[5, 0, 1, 2, 3]`. -/
def spec_deque_extendLeft_reverses (impl : RepoImpl) : Prop :=
  impl.queues.deque_extendLeft (DoubleEndedQueue.fromList [1, 2, 3]) [0, 5] =
    DoubleEndedQueue.fromList [5, 0, 1, 2, 3]

/-- Popping from a singleton deque `[42]` yields `some (42, [])`. -/
def spec_deque_pop_singleton (impl : RepoImpl) : Prop :=
  impl.queues.deque_pop (DoubleEndedQueue.fromList [42]) =
    some (42, DoubleEndedQueue.fromList ([] : List Nat))

/-- Popping after appending 3 to `[1, 2]` recovers 3 from the right end. -/
def spec_deque_pop_after_append (impl : RepoImpl) : Prop :=
  impl.queues.deque_pop
    (impl.queues.deque_append (DoubleEndedQueue.fromList [1, 2]) 3) =
      some (3, DoubleEndedQueue.fromList [1, 2])

/-- Popping from the left of a singleton deque `[42]` yields `some (42, [])`. -/
def spec_deque_popLeft_singleton (impl : RepoImpl) : Prop :=
  impl.queues.deque_popLeft (DoubleEndedQueue.fromList [42]) =
    some (42, DoubleEndedQueue.fromList ([] : List Nat))

/-- Prepending 1 to `[2, 3]` and then popping from the left recovers 1. -/
def spec_deque_popLeft_after_appendLeft (impl : RepoImpl) : Prop :=
  impl.queues.deque_popLeft
    (impl.queues.deque_appendLeft (DoubleEndedQueue.fromList [2, 3]) 1) =
      some (1, DoubleEndedQueue.fromList [2, 3])
