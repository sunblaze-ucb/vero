import Heap.Harness

/-!
# Heap.Spec.BinomialHeap

Specifications for the integer binomial min-heap (BinomialHeap.lean). Each `spec_*` is a property over an
arbitrary `impl : RepoImpl`.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- Count occurrences of an integer in a list. -/
def spec_helper_binomial_countInt (x : Int) : List Int → Nat
  | [] => 0
  | y :: ys => (if x == y then 1 else 0) + spec_helper_binomial_countInt x ys

/-- Check that the first `size` elements of `h` satisfy the min-heap property
(every parent ≤ its children within the active prefix). This is the representation
invariant of the array-backed binomial min-heap. -/
def spec_helper_is_min_heap_list_int (h : List Int) (size : Nat) : Bool :=
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

/-- A `BinomialHeap` with an empty backing list is considered empty. -/
def spec_binomialheap_is_empty_initial (impl : RepoImpl) : Prop :=
  impl.heap.binomialHeapIsEmpty { heap := [] } = true

/-- `is_empty h` is `true` iff `h.heap.length = 0`. -/
def spec_binomialheap_is_empty_iff_length_zero (impl : RepoImpl) : Prop :=
  ∀ (h : BinomialHeap),
    impl.heap.binomialHeapIsEmpty h = (h.heap.length == 0)

/-- Inserting any value into any `BinomialHeap` makes it non-empty. -/
def spec_binomialheap_insert_makes_nonempty (impl : RepoImpl) : Prop :=
  ∀ (h : BinomialHeap) (v : Int),
    impl.heap.binomialHeapIsEmpty (impl.heap.binomialHeapInsert h v) = false

/-- After inserting a value, the underlying heap list grows by exactly one element. -/
def spec_binomialheap_insert_size_grows (impl : RepoImpl) : Prop :=
  ∀ (h : BinomialHeap) (v : Int),
    (impl.heap.binomialHeapInsert h v).heap.length = h.heap.length + 1

/-- Insert preserves all old elements and adds exactly one copy of the inserted value. -/
def spec_binomialheap_insert_preserves_multiset (impl : RepoImpl) : Prop :=
  ∀ (h : BinomialHeap) (v x : Int),
    spec_helper_binomial_countInt x (impl.heap.binomialHeapInsert h v).heap =
      spec_helper_binomial_countInt x h.heap + if x == v then 1 else 0

/-- `peek` of a single-element heap returns the inserted value. -/
def spec_binomialheap_peek_after_insert_empty (impl : RepoImpl) : Prop :=
  ∀ v : Int,
    impl.heap.binomialHeapPeek
      (impl.heap.binomialHeapInsert { heap := [] } v) = v

/-- After inserting 10, 3, 7, `peek` returns 3 (the minimum). -/
def spec_binomialheap_peek_min_concrete (impl : RepoImpl) : Prop :=
  impl.heap.binomialHeapPeek
    (impl.heap.binomialHeapInsert
      (impl.heap.binomialHeapInsert
        (impl.heap.binomialHeapInsert { heap := [] } 10) 3) 7) = 3

/-- Deleting the minimum from a one-element heap returns that element and leaves the heap empty. -/
def spec_binomialheap_delete_min_singleton_empties (impl : RepoImpl) : Prop :=
  ∀ v : Int,
    let (removed, h') := impl.heap.binomialHeapDeleteMin
      (impl.heap.binomialHeapInsert { heap := [] } v)
    removed = v ∧ impl.heap.binomialHeapIsEmpty h' = true

/-- On a non-empty heap, `delete_min` reduces the underlying list length by exactly one. -/
def spec_binomialheap_delete_min_size_shrinks (impl : RepoImpl) : Prop :=
  ∀ (h : BinomialHeap),
    ¬ h.heap.isEmpty →
    (impl.heap.binomialHeapDeleteMin h).2.heap.length = h.heap.length - 1

/-- After inserting 10, 3, 7, `delete_min` returns 3 (the minimum). -/
def spec_binomialheap_delete_min_returns_min_concrete (impl : RepoImpl) : Prop :=
  (impl.heap.binomialHeapDeleteMin
    (impl.heap.binomialHeapInsert
      (impl.heap.binomialHeapInsert
        (impl.heap.binomialHeapInsert { heap := [] } 10) 3) 7)).1 = 3

/-- After inserting `v`, the visible minimum (via `peek`) is no larger than `v`.
Requires `h` to be a valid min-heap (the representation invariant of the array-backed
binomial heap); `insert` maintains, but does not repair, this invariant. -/
def spec_binomialheap_peek_after_insert_le_inserted (impl : RepoImpl) : Prop :=
  ∀ (h : BinomialHeap) (v : Int),
    spec_helper_is_min_heap_list_int h.heap h.heap.length = true →
    impl.heap.binomialHeapPeek (impl.heap.binomialHeapInsert h v) ≤ v

/-- Inserting into a non-empty heap cannot raise the visible minimum. -/
def spec_binomialheap_peek_after_insert_le_old_peek (impl : RepoImpl) : Prop :=
  ∀ (h : BinomialHeap) (v : Int),
    impl.heap.binomialHeapIsEmpty h = false →
    impl.heap.binomialHeapPeek (impl.heap.binomialHeapInsert h v)
      ≤ impl.heap.binomialHeapPeek h

/-- On a non-empty heap, `delete_min` returns the same value `peek` observes. -/
def spec_binomialheap_delete_min_returns_peek (impl : RepoImpl) : Prop :=
  ∀ (h : BinomialHeap),
    impl.heap.binomialHeapIsEmpty h = false →
    (impl.heap.binomialHeapDeleteMin h).1 = impl.heap.binomialHeapPeek h

/-- `delete_min` removes exactly one copy of the returned minimum and preserves the rest. -/
def spec_binomialheap_delete_min_preserves_multiset (impl : RepoImpl) : Prop :=
  ∀ (h : BinomialHeap) (x : Int),
    impl.heap.binomialHeapIsEmpty h = false →
      let r := impl.heap.binomialHeapDeleteMin h
      spec_helper_binomial_countInt x h.heap =
        spec_helper_binomial_countInt x r.2.heap + if x == r.1 then 1 else 0

/-- If `delete_min` leaves a non-empty heap, the new minimum is no smaller than the
removed minimum. Requires `h` to be a valid min-heap (the representation invariant of
the array-backed binomial heap); `delete_min` assumes, and does not repair, this invariant. -/
def spec_binomialheap_delete_min_next_peek_ge_removed (impl : RepoImpl) : Prop :=
  ∀ (h : BinomialHeap),
    spec_helper_is_min_heap_list_int h.heap h.heap.length = true →
    impl.heap.binomialHeapIsEmpty h = false →
    impl.heap.binomialHeapIsEmpty (impl.heap.binomialHeapDeleteMin h).2 = false →
    (impl.heap.binomialHeapDeleteMin h).1
      ≤ impl.heap.binomialHeapPeek (impl.heap.binomialHeapDeleteMin h).2
