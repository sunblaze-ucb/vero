import Heap.Harness

/-!
# Heap.Spec.Interfile

Cross-implementation specifications relating two or more heap APIs in the bundle.
Each `spec_*` is a property over an arbitrary `impl : RepoImpl`.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- Check that the first `size` elements of `h` satisfy the max-heap property
(every parent ≥ its children within the active prefix). Local copy of the
representation invariant used by well-formedness preconditions below. -/
def spec_helper_interfile_is_max_heap_list_int (h : List Int) (size : Nat) : Bool :=
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

/-- Check that the first `size` elements of `h` satisfy the min-heap property
(every parent ≤ its children within the active prefix). Local copy used by the
binomial-heap well-formedness precondition below. -/
def spec_helper_interfile_is_min_heap_list_int (h : List Int) (size : Nat) : Bool :=
  (List.range size).all fun i =>
    let pv := h[i]?
    let lv := h[2 * i + 1]?
    let rv := h[2 * i + 2]?
    (match pv, lv with
      | some p, some l =>
        if 2 * i + 1 ≥ size then true else decide (p ≤ l)
      | _, _ => true) &&
    (match pv, rv with
      | some p, some r =>
        if 2 * i + 2 ≥ size then true else decide (p ≤ r)
      | _, _ => true)

/-- The `BinaryHeap` and polymorphic `Heap` max-heap APIs agree on the maximum
extracted from the same observed array contents. Requires `binary` to be a valid
max-heap over its full backing list, so its root (`binaryHeapPop`'s list head) is the
true maximum of the shared contents; equal *contents* alone do not imply equal *order*. -/
def spec_interfile_binary_heap_extract_max_agree (impl : RepoImpl) : Prop :=
  ∀ (binary : BinaryHeap) (heap : Heap Int) (collection : List Int)
    (v : Int) (h' : Heap Int),
    spec_helper_interfile_is_max_heap_list_int binary.data binary.data.length = true →
    impl.heap.binaryHeapGetList binary = collection →
    impl.heap.heapExtractMax (impl.heap.heapBuildMaxHeap heap collection)
      = some (v, h') →
    (impl.heap.binaryHeapPop binary).1 = v

/-- After inserting `value` into both max-heap APIs, the subsequent maximum
extraction is at least as large as `value` in each API. Requires both heaps to be valid
max-heaps (with the polymorphic `Heap`'s active size equal to its list length): `insert`
maintains, but does not repair, the max-heap invariant, so a malformed input could leave
the inserted value shadowed by a pre-existing violation. -/
def spec_interfile_binary_heap_insert_then_max_ge_inserted
    (impl : RepoImpl) : Prop :=
  ∀ (binary : BinaryHeap) (heap : Heap Int) (value : Int)
    (m : Int) (h' : Heap Int),
    spec_helper_interfile_is_max_heap_list_int binary.data binary.data.length = true →
    heap.h.length = heap.heap_size →
    spec_helper_interfile_is_max_heap_list_int heap.h heap.heap_size = true →
    impl.heap.heapExtractMax (impl.heap.heapInsert heap value) = some (m, h') →
    value ≤ (impl.heap.binaryHeapPop (impl.heap.binaryHeapInsert binary value)).1
      ∧ value ≤ m

/-- The `BinaryHeap` size and the input collection length agree, and the public list
length matches the collection length, when the public list equals the collection. -/
def spec_interfile_binary_heap_observed_size_agree (impl : RepoImpl) : Prop :=
  ∀ (binary : BinaryHeap) (collection : List Int),
    impl.heap.binaryHeapGetList binary = collection →
    impl.heap.binaryHeapSize binary = collection.length
      ∧ (impl.heap.binaryHeapGetList binary).length = collection.length

/-- Popping the binary max heap and extracting from the array-backed max heap both
return members of the same observed input collection. -/
def spec_interfile_binary_heap_removed_values_mem (impl : RepoImpl) : Prop :=
  ∀ (binary : BinaryHeap) (heap : Heap Int) (collection : List Int)
    (v : Int) (h' : Heap Int),
    impl.heap.binaryHeapGetList binary = collection →
    impl.heap.heapExtractMax (impl.heap.heapBuildMaxHeap heap collection)
      = some (v, h') →
    (impl.heap.binaryHeapPop binary).1 ∈ collection ∧ v ∈ collection

/-- Binomial and skew min-heaps expose the same minimum after the same insert when
their previous visible minima agree. Requires `binomial` to be a valid min-heap so its
`peek` reports the true minimum; `insert` maintains, but does not repair, that invariant.
(No skew invariant is needed: `skewHeapInsert` merges the heap with a singleton and the
resulting top is `min(oldMin, value)` regardless of the tree's internal shape.) -/
def spec_interfile_binomial_skew_insert_top_agree (impl : RepoImpl) : Prop :=
  ∀ (binomial : BinomialHeap) (skew : SkewHeap Int) (value oldMin : Int),
    spec_helper_interfile_is_min_heap_list_int binomial.heap binomial.heap.length = true →
    impl.heap.binomialHeapIsEmpty binomial = false →
    impl.heap.binomialHeapPeek binomial = oldMin →
    impl.heap.skewHeapTop skew = some oldMin →
    impl.heap.skewHeapTop (impl.heap.skewHeapInsert skew value)
      = some (impl.heap.binomialHeapPeek
                (impl.heap.binomialHeapInsert binomial value))

/-- Binomial `delete_min` and skew `pop` return the same value when their visible
minima agree. -/
def spec_interfile_binomial_skew_remove_min_agree (impl : RepoImpl) : Prop :=
  ∀ (binomial : BinomialHeap) (skew : SkewHeap Int) (minValue : Int),
    impl.heap.binomialHeapIsEmpty binomial = false →
    impl.heap.binomialHeapPeek binomial = minValue →
    impl.heap.skewHeapTop skew = some minValue →
    (impl.heap.binomialHeapDeleteMin binomial).1 = minValue
      ∧ (impl.heap.skewHeapPop skew).1 = some minValue

/-- Randomized and skew min-heaps expose the same top when their `to_sorted_list` head
and `top` views agree on a common value. -/
def spec_interfile_randomized_skew_top_agree (impl : RepoImpl) : Prop :=
  ∀ (randomized : RandomizedHeap Int) (skew : SkewHeap Int)
    (value : Int) (rest : List Int),
    impl.heap.randomizedHeapToSortedList randomized = value :: rest →
    impl.heap.skewHeapTop skew = some value →
    impl.heap.randomizedHeapTop randomized = impl.heap.skewHeapTop skew

/-- Clearing either meldable min-heap leaves no observable top, and the two cleared
APIs agree (both report `none`). -/
def spec_interfile_randomized_skew_clear_top_agree (impl : RepoImpl) : Prop :=
  ∀ (randomized : RandomizedHeap Int) (skew : SkewHeap Int),
    impl.heap.randomizedHeapTop (impl.heap.randomizedHeapClear randomized)
      = impl.heap.skewHeapTop (impl.heap.skewHeapClear skew)

/-- Randomized and skew min-heaps expose the same minimum after the same insert when
their previous visible minima agree. -/
def spec_interfile_randomized_skew_insert_top_agree (impl : RepoImpl) : Prop :=
  ∀ (randomized : RandomizedHeap Int) (skew : SkewHeap Int)
    (value oldMin : Int),
    impl.heap.randomizedHeapTop randomized = some oldMin →
    impl.heap.skewHeapTop skew = some oldMin →
    impl.heap.randomizedHeapTop
        (impl.heap.randomizedHeapInsert randomized value)
      = impl.heap.skewHeapTop (impl.heap.skewHeapInsert skew value)
