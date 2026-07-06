import Heap.Harness

/-!
# Heap.Spec.MinHeap

Specifications for the named-node min-heap (MinHeap.lean). Each `spec_*` is a property over an
arbitrary `impl : RepoImpl`.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- `get_parent_idx` is exactly `(i - 1) / 2` for any integer index. -/
def spec_get_parent_idx_formula (impl : RepoImpl) : Prop :=
  ∀ (h : MinHeap) (i : Int),
    impl.heap.minHeapGetParentIdx h i = (i - 1) / 2

/-- Applying `get_parent_idx` to the root (index 0) returns −1. -/
def spec_get_parent_idx_root (impl : RepoImpl) : Prop :=
  ∀ (h : MinHeap),
    impl.heap.minHeapGetParentIdx h 0 = -1

/-- `get_left_child_idx i` returns `2 * i + 1` for any integer index. -/
def spec_get_left_child_idx_formula (impl : RepoImpl) : Prop :=
  ∀ (h : MinHeap) (i : Int),
    impl.heap.minHeapGetLeftChildIdx h i = 2 * i + 1

/-- `get_right_child_idx i` returns `2 * i + 2` for any integer index. -/
def spec_get_right_child_idx_formula (impl : RepoImpl) : Prop :=
  ∀ (h : MinHeap) (i : Int),
    impl.heap.minHeapGetRightChildIdx h i = 2 * i + 2

/-- For any non-negative index, navigating to the left child and back returns the original index. -/
def spec_left_then_parent_inverse (impl : RepoImpl) : Prop :=
  ∀ (h : MinHeap) (i : Int),
    i ≥ 0 →
    impl.heap.minHeapGetParentIdx h (impl.heap.minHeapGetLeftChildIdx h i) = i

/-- For any non-negative index, navigating to the right child and back returns the original index. -/
def spec_right_then_parent_inverse (impl : RepoImpl) : Prop :=
  ∀ (h : MinHeap) (i : Int),
    i ≥ 0 →
    impl.heap.minHeapGetParentIdx h (impl.heap.minHeapGetRightChildIdx h i) = i

/-- The right child index is exactly one more than the left child index. -/
def spec_minheap_left_right_differ_by_one (impl : RepoImpl) : Prop :=
  ∀ (h : MinHeap) (i : Int),
    impl.heap.minHeapGetRightChildIdx h i =
      impl.heap.minHeapGetLeftChildIdx h i + 1

/-- `is_empty h` is `true` iff the underlying `heap` list is empty. -/
def spec_is_empty_iff_heap_empty (impl : RepoImpl) : Prop :=
  ∀ (h : MinHeap),
    impl.heap.minHeapIsEmpty h = h.heap.isEmpty
