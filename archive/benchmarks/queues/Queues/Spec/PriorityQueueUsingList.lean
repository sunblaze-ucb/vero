import Queues.Harness
import Queues.Spec.Aux

/-!
# Queues.Spec.PriorityQueueUsingList

Ordering and removal laws for fixed-priority and element-priority queues.
-/

/-- Empty fixed-priority queues cannot be dequeued. -/
def spec_fpq_empty_dequeue (impl : RepoImpl) : Prop :=
  impl.queues.fpq_dequeue (FixedPriorityQueue.new (α := Nat)) = none

/-- Enqueueing at the same fixed priority is FIFO within that priority bucket. -/
def spec_fpq_fifo_within_priority (impl : RepoImpl) : Prop :=
  ∀ (x y : Nat),
    impl.queues.fpq_dequeue
        (impl.queues.fpq_enqueue
          (impl.queues.fpq_enqueue (FixedPriorityQueue.new (α := Nat)) 1 x)
          1 y) =
      some (x, { (FixedPriorityQueue.new (α := Nat)) with prio1 := [y] })

/-- Enqueueing at a valid non-full fixed priority appends to exactly that bucket. -/
def spec_fpq_enqueue_valid_priority_appends (impl : RepoImpl) : Prop :=
  ∀ {α : Type} (q : FixedPriorityQueue α) (x : α),
    (spec_helper_len q.prio0 < 100 →
      impl.queues.fpq_enqueue q 0 x = { q with prio0 := q.prio0 ++ [x] }) ∧
    (spec_helper_len q.prio1 < 100 →
      impl.queues.fpq_enqueue q 1 x = { q with prio1 := q.prio1 ++ [x] }) ∧
    (spec_helper_len q.prio2 < 100 →
      impl.queues.fpq_enqueue q 2 x = { q with prio2 := q.prio2 ++ [x] })

/-- Fixed-priority dequeue prefers priority 0 over 1 over 2 regardless of enqueue order. -/
def spec_fpq_priority_order (impl : RepoImpl) : Prop :=
  ∀ (low mid high : Nat),
    let q0 := FixedPriorityQueue.new (α := Nat)
    let q1 := impl.queues.fpq_enqueue q0 2 low
    let q2 := impl.queues.fpq_enqueue q1 1 mid
    let q3 := impl.queues.fpq_enqueue q2 0 high
    impl.queues.fpq_dequeue q3 = some (high, q2)

/-- Invalid fixed priorities leave the queue unchanged. -/
def spec_fpq_invalid_priority_noop (impl : RepoImpl) : Prop :=
  ∀ {α : Type} (q : FixedPriorityQueue α) (priority : Nat) (x : α),
    priority ≠ 0 →
    priority ≠ 1 →
    priority ≠ 2 →
      impl.queues.fpq_enqueue q priority x = q

/-- Empty element-priority queues cannot be dequeued. -/
def spec_epq_empty_dequeue (impl : RepoImpl) : Prop :=
  impl.queues.epq_dequeue (ElementPriorityQueue.new (α := Nat)) = none

/-- Element-priority enqueue appends one element without reordering existing elements. -/
def spec_epq_enqueue_appends (impl : RepoImpl) : Prop :=
  ∀ {α : Type} (q : ElementPriorityQueue α) (x : α),
    impl.queues.epq_enqueue q x = q ++ [x]

/-- Dequeueing a nonempty Nat element-priority queue returns a minimum and removes one copy. -/
def spec_epq_dequeue_returns_min_and_erases (impl : RepoImpl) : Prop :=
  ∀ (x : Nat) (xs : List Nat),
    let q : ElementPriorityQueue Nat := x :: xs
    ∃ (m : Nat) (rest : ElementPriorityQueue Nat),
      impl.queues.epq_dequeue q = some (m, rest) ∧
      m ∈ q ∧
      rest = q.erase m ∧
      ∀ y, y ∈ q → m ≤ y

-- ── Restored from pre-T1B backup ──────────────────────────────
-- Restored specs for PriorityQueueUsingList

/-- Enqueueing element 10 at priority 0 and immediately dequeueing returns `some 10`. -/
def spec_fpq_enqueue_dequeue_p0 (impl : RepoImpl) : Prop :=
  (impl.queues.fpq_dequeue
    (impl.queues.fpq_enqueue (FixedPriorityQueue.new (α := Nat)) 0 10)).map
      (fun p => p.fst) = some 10

/-- Enqueueing element 7 at priority 1 and dequeueing returns `some 7`. -/
def spec_fpq_enqueue_dequeue_p1 (impl : RepoImpl) : Prop :=
  (impl.queues.fpq_dequeue
    (impl.queues.fpq_enqueue (FixedPriorityQueue.new (α := Nat)) 1 7)).map
      (fun p => p.fst) = some 7

/-- Enqueueing element 42 at priority 2 and dequeueing returns `some 42`. -/
def spec_fpq_enqueue_dequeue_p2 (impl : RepoImpl) : Prop :=
  (impl.queues.fpq_dequeue
    (impl.queues.fpq_enqueue (FixedPriorityQueue.new (α := Nat)) 2 42)).map
      (fun p => p.fst) = some 42

/-- Priority 0 (highest) beats priority 2 (lowest): element 1 at p=0 dequeues
    before element 99 at p=2. -/
def spec_fpq_priority_zero_wins (impl : RepoImpl) : Prop :=
  (impl.queues.fpq_dequeue
    (impl.queues.fpq_enqueue
      (impl.queues.fpq_enqueue (FixedPriorityQueue.new (α := Nat)) 2 99) 0 1)).map
        (fun p => p.fst) = some 1

/-- Enqueueing 10 into an empty element-priority queue and dequeueing returns `some 10`. -/
def spec_epq_enqueue_dequeue_singleton (impl : RepoImpl) : Prop :=
  (impl.queues.epq_dequeue
    (impl.queues.epq_enqueue (ElementPriorityQueue.new (α := Nat)) 10)).map
      (fun p => p.fst) = some 10

/-- Enqueueing 5 then 3, dequeueing returns the minimum (3). -/
def spec_epq_dequeue_minimum_5_3 (impl : RepoImpl) : Prop :=
  (impl.queues.epq_dequeue
    (impl.queues.epq_enqueue
      (impl.queues.epq_enqueue (ElementPriorityQueue.new (α := Nat)) 5) 3)).map
        (fun p => p.fst) = some 3

/-- Enqueueing 7 then 9, dequeueing returns the minimum (7). -/
def spec_epq_dequeue_minimum_7_9 (impl : RepoImpl) : Prop :=
  (impl.queues.epq_dequeue
    (impl.queues.epq_enqueue
      (impl.queues.epq_enqueue (ElementPriorityQueue.new (α := Nat)) 7) 9)).map
        (fun p => p.fst) = some 7

/-- Enqueueing 4, 1, 8 in that order, dequeueing returns the minimum (1). -/
def spec_epq_dequeue_minimum_4_1_8 (impl : RepoImpl) : Prop :=
  (impl.queues.epq_dequeue
    (impl.queues.epq_enqueue
      (impl.queues.epq_enqueue
        (impl.queues.epq_enqueue (ElementPriorityQueue.new (α := Nat)) 4) 1) 8)).map
          (fun p => p.fst) = some 1
