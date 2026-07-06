import Heap.Harness

/-!
# Heap.Spec.Heap

Specifications for the polymorphic max-heap (Heap.lean). Each `spec_*` is a property over an
arbitrary `impl : RepoImpl`.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- Check that a list of Int is sorted in non-decreasing order. -/
def spec_helper_is_sorted_asc_int : List Int → Bool
  | []           => true
  | [_]          => true
  | x :: y :: xs => decide (x ≤ y) && spec_helper_is_sorted_asc_int (y :: xs)

/-- Check that the first `size` elements of `h` satisfy the max-heap property
(every parent ≥ its children within the active prefix). -/
def spec_helper_is_max_heap_list_int (h : List Int) (size : Nat) : Bool :=
  (List.range size).all fun i =>
    let pv := h[i]?
    let lv := h[2 * i + 1]?
    let rv := h[2 * i + 2]?
    (match pv, lv with
      | some p, some l =>
        if 2 * i + 1 ≥ size then true else decide (l ≤ p)
      | _, _ => true) &&
    (match pv, rv with
      | some p, some r =>
        if 2 * i + 2 ≥ size then true else decide (r ≤ p)
      | _, _ => true)

/-- Count occurrences of an integer in a list. -/
def spec_helper_heap_countInt (x : Int) : List Int → Nat
  | [] => 0
  | y :: ys => (if x == y then 1 else 0) + spec_helper_heap_countInt x ys

/-- The parent index of the root node (index 0) is always `none`. -/
def spec_parent_index_root_none (impl : RepoImpl) : Prop :=
  ∀ (h : Heap Int),
    impl.heap.heapParentIndex h 0 = none

/-- For any positive child index `i`, the parent index is `(i - 1) / 2`. -/
def spec_parent_index_formula (impl : RepoImpl) : Prop :=
  ∀ (h : Heap Int) (i : Nat),
    i > 0 → impl.heap.heapParentIndex h i = some ((i - 1) / 2)

/-- `left_child_idx` returns `some (2p + 1)` when in bounds, else `none`. -/
def spec_left_child_idx_formula (impl : RepoImpl) : Prop :=
  ∀ (h : Heap Int) (p : Nat),
    impl.heap.heapLeftChildIdx h p =
      if 2 * p + 1 < h.heap_size then some (2 * p + 1) else none

/-- `right_child_idx` returns `some (2p + 2)` when in bounds, else `none`. -/
def spec_right_child_idx_formula (impl : RepoImpl) : Prop :=
  ∀ (h : Heap Int) (p : Nat),
    impl.heap.heapRightChildIdx h p =
      if 2 * p + 2 < h.heap_size then some (2 * p + 2) else none

/-- When both children exist, the right child index is exactly one more than the left. -/
def spec_left_right_differ_by_one (impl : RepoImpl) : Prop :=
  ∀ (h : Heap Int) (p : Nat) (lc rc : Nat),
    impl.heap.heapLeftChildIdx h p = some lc →
    impl.heap.heapRightChildIdx h p = some rc →
    rc = lc + 1

/-- `parent_index` is a partial left-inverse of `left_child_idx`. -/
def spec_parent_left_inverse (impl : RepoImpl) : Prop :=
  ∀ (h : Heap Int) (p : Nat) (lc : Nat),
    impl.heap.heapLeftChildIdx h p = some lc →
    impl.heap.heapParentIndex h lc = some p

/-- After `build_max_heap`, `heap_size` and list length both equal `xs.length`. -/
def spec_build_max_heap_size (impl : RepoImpl) : Prop :=
  ∀ (h0 : Heap Int) (xs : List Int),
    let h := impl.heap.heapBuildMaxHeap h0 xs
    h.heap_size = xs.length ∧ h.h.length = xs.length

/-- Pinned concrete output for `build_max_heap` on the canonical 11-element input. -/
def spec_build_max_heap_concrete (impl : RepoImpl) : Prop :=
  (impl.heap.heapBuildMaxHeap (α := Int) { h := [], heap_size := 0 }
    [103, 9, 1, 7, 11, 15, 25, 201, 209, 107, 5]).h
  = [209, 201, 25, 103, 107, 15, 1, 9, 7, 11, 5]

/-- The output of `build_max_heap` satisfies the max-heap property. -/
def spec_build_max_heap_property (impl : RepoImpl) : Prop :=
  ∀ (h0 : Heap Int) (xs : List Int),
    let h := impl.heap.heapBuildMaxHeap h0 xs
    spec_helper_is_max_heap_list_int h.h h.heap_size = true

/-- `build_max_heap` preserves exactly the input elements. -/
def spec_build_max_heap_preserves_multiset (impl : RepoImpl) : Prop :=
  ∀ (h0 : Heap Int) (xs : List Int) (x : Int),
    spec_helper_heap_countInt x (impl.heap.heapBuildMaxHeap h0 xs).h =
      spec_helper_heap_countInt x xs

/-- Extracting the maximum from an empty heap returns `none`. -/
def spec_extract_max_empty (impl : RepoImpl) : Prop :=
  ∀ (h : Heap Int),
    h.heap_size = 0 →
    impl.heap.heapExtractMax h = none

/-- On a non-empty heap whose active size does not exceed its backing list,
`extract_max` decreases `heap_size` by exactly 1. The `heap_size ≤ h.h.length` bound
ensures the extremum and last-element lookups are in range (the `Heap` structure
permits `heap_size` to exceed the list length). -/
def spec_extract_max_size_decreases (impl : RepoImpl) : Prop :=
  ∀ (h : Heap Int),
    h.heap_size > 0 →
    h.heap_size ≤ h.h.length →
    ∃ v h', impl.heap.heapExtractMax h = some (v, h') ∧
            h'.heap_size = h.heap_size - 1

/-- `extract_max` returns 209 on the canonical 11-element max-heap. -/
def spec_extract_max_returns_max (impl : RepoImpl) : Prop :=
  (impl.heap.heapExtractMax (α := Int)
    { h := [209, 201, 25, 103, 107, 15, 1, 9, 7, 11, 5], heap_size := 11 }).map Prod.fst
  = some 209

/-- Inserting any value increases `heap_size` by exactly 1. -/
def spec_insert_size_grows (impl : RepoImpl) : Prop :=
  ∀ (h : Heap Int) (v : Int),
    (impl.heap.heapInsert h v).heap_size = h.heap_size + 1

/-- Inserting into the empty heap produces `h = [v]`. -/
def spec_insert_into_empty (impl : RepoImpl) : Prop :=
  ∀ v : Int,
    (impl.heap.heapInsert (α := Int) { h := [], heap_size := 0 } v).h = [v]

/-- Inserting `v` into empty then extracting the max returns `v`. -/
def spec_extract_after_insert_empty (impl : RepoImpl) : Prop :=
  ∀ (v : Int),
    let h := impl.heap.heapInsert (α := Int) { h := [], heap_size := 0 } v
    (impl.heap.heapExtractMax h).map Prod.fst = some v

/-- Sorting an empty heap returns an empty underlying list. -/
def spec_heap_sort_empty (impl : RepoImpl) : Prop :=
  (impl.heap.heapHeapSort (α := Int) { h := [], heap_size := 0 }).h = []

/-- Sorting a singleton heap returns the element unchanged. -/
def spec_heap_sort_singleton (impl : RepoImpl) : Prop :=
  ∀ v : Int,
    (impl.heap.heapHeapSort (α := Int) { h := [v], heap_size := 1 }).h = [v]

/-- Pinned concrete sorted output for the canonical 11-element max-heap. -/
def spec_heap_sort_concrete_sorted (impl : RepoImpl) : Prop :=
  (impl.heap.heapHeapSort (α := Int)
    { h := [209, 201, 25, 103, 107, 15, 1, 9, 7, 11, 5], heap_size := 11 }).h
  = [1, 5, 7, 9, 11, 15, 25, 103, 107, 201, 209]

/-- `build_max_heap` followed by `heap_sort` produces a non-decreasingly sorted list. -/
def spec_heap_sort_sorted (impl : RepoImpl) : Prop :=
  ∀ (h0 : Heap Int) (xs : List Int),
    xs ≠ [] →
    spec_helper_is_sorted_asc_int
      (impl.heap.heapHeapSort (impl.heap.heapBuildMaxHeap h0 xs)).h = true

/-- `heap_sort` preserves exactly the elements in the heap list. -/
def spec_heap_sort_preserves_multiset (impl : RepoImpl) : Prop :=
  ∀ (h : Heap Int) (x : Int),
    spec_helper_heap_countInt x (impl.heap.heapHeapSort h).h =
      spec_helper_heap_countInt x h.h

/-- After `build_max_heap`, if `extract_max` succeeds, the extracted value comes from
the input collection. -/
def spec_build_max_heap_extract_mem (impl : RepoImpl) : Prop :=
  ∀ (h0 : Heap Int) (xs : List Int) (v : Int) (h' : Heap Int),
    impl.heap.heapExtractMax (impl.heap.heapBuildMaxHeap h0 xs) = some (v, h') →
    v ∈ xs

/-- After `build_max_heap`, if `extract_max` succeeds, the extracted value is at least
as large as every value in the input collection. -/
def spec_build_max_heap_extract_max (impl : RepoImpl) : Prop :=
  ∀ (h0 : Heap Int) (xs : List Int) (v : Int) (h' : Heap Int),
    impl.heap.heapExtractMax (impl.heap.heapBuildMaxHeap h0 xs) = some (v, h') →
    ∀ y, y ∈ xs → y ≤ v

/-- After inserting a value into a well-formed max-heap, a subsequent `extract_max`
(when it succeeds) returns a value at least as large as the inserted value. Requires
`h` to be a valid max-heap with active size equal to its list length: `insert`
maintains the max-heap invariant on such inputs (so the inserted value participates in
the active heap), but does not repair a pre-existing violation. -/
def spec_insert_extract_max_ge_inserted (impl : RepoImpl) : Prop :=
  ∀ (h : Heap Int) (v : Int) (m : Int) (h' : Heap Int),
    h.h.length = h.heap_size →
    spec_helper_is_max_heap_list_int h.h h.heap_size = true →
    impl.heap.heapExtractMax (impl.heap.heapInsert h v) = some (m, h') →
    v ≤ m

/-- Sorting a well-formed max-heap produces a non-decreasingly sorted list. `heap_sort`
assumes its input already satisfies the max-heap property (it is the in-place tail of
heapsort, run after `build_max_heap`); its output is an ascending list, not itself a
max-heap, so it is *not* idempotent — this states the genuine contract instead. -/
def spec_heap_sort_valid_heap_sorted (impl : RepoImpl) : Prop :=
  ∀ (h : Heap Int),
    h.h.length = h.heap_size →
    spec_helper_is_max_heap_list_int h.h h.heap_size = true →
    spec_helper_is_sorted_asc_int (impl.heap.heapHeapSort h).h = true
