import Heap.Harness

/-!
# Heap.Spec.RandomizedHeap

Specifications for the polymorphic randomized min-heap (RandomizedHeap.lean). Each `spec_*` is a property over an
arbitrary `impl : RepoImpl`.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- Number of nodes in a randomized-heap tree. Used to bound spec claims below the
implementation's fixed recursion-fuel limit (1024). -/
def spec_helper_randomized_size : Option (RandomizedHeapNode Int) → Nat
  | none => 0
  | some (.mk _ l r) => 1 + spec_helper_randomized_size l + spec_helper_randomized_size r

/-- Check that a randomized-heap tree satisfies the min-heap order property: every node's
value is ≤ the value of each of its children, recursively. This is the representation
invariant maintained by the randomized-heap API. -/
def spec_helper_randomized_is_min_heap : Option (RandomizedHeapNode Int) → Bool
  | none => true
  | some (.mk v l r) =>
    (match l with | some (.mk lv _ _) => decide (v ≤ lv) | none => true) &&
    (match r with | some (.mk rv _ _) => decide (v ≤ rv) | none => true) &&
    spec_helper_randomized_is_min_heap l && spec_helper_randomized_is_min_heap r

/-- `top` of an empty randomized heap returns `none`. -/
def spec_randomizedheap_top_empty (impl : RepoImpl) : Prop :=
  impl.heap.randomizedHeapTop (α := Int) { _root := none } = none

/-- `top` of a single-element heap (inserting `v` into empty) is `some v`. -/
def spec_randomizedheap_top_after_insert_empty (impl : RepoImpl) : Prop :=
  ∀ (v : Int),
    impl.heap.randomizedHeapTop
      (impl.heap.randomizedHeapInsert (α := Int) { _root := none } v) = some v

/-- `to_sorted_list` of an empty randomized heap returns the empty list. -/
def spec_randomizedheap_to_sorted_list_empty (impl : RepoImpl) : Prop :=
  impl.heap.randomizedHeapToSortedList (α := Int) { _root := none } = []

/-- `to_sorted_list` of a one-element heap returns a singleton list containing that value. -/
def spec_randomizedheap_to_sorted_list_singleton (impl : RepoImpl) : Prop :=
  ∀ v : Int,
    impl.heap.randomizedHeapToSortedList
      (impl.heap.randomizedHeapInsert (α := Int) { _root := none } v) = [v]

/-- After inserting 5, 3, 7, `to_sorted_list` returns `[3, 5, 7]` (ascending order). -/
def spec_randomizedheap_to_sorted_list_sorted_concrete (impl : RepoImpl) : Prop :=
  impl.heap.randomizedHeapToSortedList
    (impl.heap.randomizedHeapInsert
      (impl.heap.randomizedHeapInsert
        (impl.heap.randomizedHeapInsert (α := Int) { _root := none } 5) 3) 7)
  = [3, 5, 7]

/-- The first element of `to_sorted_list h` equals `top h`. -/
def spec_randomizedheap_to_sorted_list_head_is_top (impl : RepoImpl) : Prop :=
  ∀ (h : RandomizedHeap Int),
    (impl.heap.randomizedHeapToSortedList h).head? =
      impl.heap.randomizedHeapTop h

/-- `top (clear h)` is always `none`. -/
def spec_randomizedheap_clear_top_none (impl : RepoImpl) : Prop :=
  ∀ (h : RandomizedHeap Int),
    impl.heap.randomizedHeapTop (impl.heap.randomizedHeapClear h) = none

/-- `to_sorted_list (clear h)` is always `[]`. -/
def spec_randomizedheap_clear_to_sorted_list_empty (impl : RepoImpl) : Prop :=
  ∀ (h : RandomizedHeap Int),
    impl.heap.randomizedHeapToSortedList (impl.heap.randomizedHeapClear h) = []

/-- Clearing twice is the same as clearing once. -/
def spec_randomizedheap_clear_idempotent (impl : RepoImpl) : Prop :=
  ∀ (h : RandomizedHeap Int),
    impl.heap.randomizedHeapClear (impl.heap.randomizedHeapClear h) =
      impl.heap.randomizedHeapClear h

/-- After inserting `v` into a heap smaller than the implementation's recursion-fuel
bound, the value is observable in `to_sorted_list`. The `< 1024` size guard is required
because both `insert` (merge) and `to_sorted_list` are bounded to 1024 recursion steps,
so on larger heaps a tail value can be truncated. -/
def spec_randomizedheap_insert_to_sorted_list_contains (impl : RepoImpl) : Prop :=
  ∀ (h : RandomizedHeap Int) (v : Int),
    spec_helper_randomized_size h._root < 1024 →
    v ∈ impl.heap.randomizedHeapToSortedList (impl.heap.randomizedHeapInsert h v)

/-- `to_sorted_list` produces a non-decreasingly sorted list. Requires `h` to satisfy the
randomized-heap min-heap-order invariant; the impl peels the root at each step and trusts
it to be the current minimum, so an unordered tree would emit an inversion. -/
def spec_randomizedheap_to_sorted_list_sorted (impl : RepoImpl) : Prop :=
  ∀ (h : RandomizedHeap Int),
    spec_helper_randomized_is_min_heap h._root = true →
    (impl.heap.randomizedHeapToSortedList h).Pairwise (· ≤ ·)
