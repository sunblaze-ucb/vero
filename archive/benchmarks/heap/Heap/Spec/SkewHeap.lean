import Heap.Harness

/-!
# Heap.Spec.SkewHeap

Specifications for the polymorphic skew min-heap (SkewHeap.lean). Each `spec_*` is a property over an
arbitrary `impl : RepoImpl`.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- Check that a skew-heap tree satisfies the min-heap order property: every node's
value is ≤ the value of each of its children, recursively. This is the representation
invariant maintained by the skew-heap API. -/
def spec_helper_skew_is_min_heap : Option (SkewNode Int) → Bool
  | none => true
  | some (.mk v l r) =>
    (match l with | some (.mk lv _ _) => decide (v ≤ lv) | none => true) &&
    (match r with | some (.mk rv _ _) => decide (v ≤ rv) | none => true) &&
    spec_helper_skew_is_min_heap l && spec_helper_skew_is_min_heap r

/-- `top` of an empty skew heap returns `none`. -/
def spec_skewheap_top_empty (impl : RepoImpl) : Prop :=
  impl.heap.skewHeapTop (α := Int) { _root := none } = none

/-- After inserting `v` into an empty skew heap, `top` returns `some v`. -/
def spec_skewheap_top_after_insert_empty (impl : RepoImpl) : Prop :=
  ∀ (v : Int),
    impl.heap.skewHeapTop
      (impl.heap.skewHeapInsert (α := Int) { _root := none } v) = some v

/-- Inserting 5 then 3 yields a heap with top = `some 3`. -/
def spec_skewheap_top_min_two_concrete (impl : RepoImpl) : Prop :=
  impl.heap.skewHeapTop
    (impl.heap.skewHeapInsert
      (impl.heap.skewHeapInsert (α := Int) { _root := none } 5) 3) = some 3

/-- Inserting 5, 3, 7 yields a heap with top = `some 3`. -/
def spec_skewheap_top_min_three_concrete (impl : RepoImpl) : Prop :=
  impl.heap.skewHeapTop
    (impl.heap.skewHeapInsert
      (impl.heap.skewHeapInsert
        (impl.heap.skewHeapInsert (α := Int) { _root := none } 5) 3) 7) = some 3

/-- Popping from an empty skew heap returns `(none, empty heap)`. -/
def spec_skewheap_pop_empty (impl : RepoImpl) : Prop :=
  let (v, h') := impl.heap.skewHeapPop (α := Int) { _root := none }
  v = none ∧ h'._root = none

/-- Popping from a single-element skew heap returns `(some v, empty)`. -/
def spec_skewheap_pop_after_insert_empty (impl : RepoImpl) : Prop :=
  ∀ (v : Int),
    let (r, h') := impl.heap.skewHeapPop
      (impl.heap.skewHeapInsert (α := Int) { _root := none } v)
    r = some v ∧ h'._root = none

/-- For any non-empty skew heap, the value returned by `pop` equals `top`. -/
def spec_skewheap_pop_returns_top (impl : RepoImpl) : Prop :=
  ∀ (h : SkewHeap Int),
    h._root.isSome →
    (impl.heap.skewHeapPop h).1 = impl.heap.skewHeapTop h

/-- After inserting 5, 3 and popping (extracts 3), the remaining heap has top = `some 5`. -/
def spec_skewheap_pop_residue_top_concrete (impl : RepoImpl) : Prop :=
  let (_, h') := impl.heap.skewHeapPop
    (impl.heap.skewHeapInsert
      (impl.heap.skewHeapInsert (α := Int) { _root := none } 5) 3)
  impl.heap.skewHeapTop h' = some 5

/-- `top (clear h)` is always `none`. -/
def spec_skewheap_clear_top_none (impl : RepoImpl) : Prop :=
  ∀ (h : SkewHeap Int),
    impl.heap.skewHeapTop (impl.heap.skewHeapClear h) = none

/-- Clearing a heap twice yields the same result as clearing once. -/
def spec_skewheap_clear_idempotent (impl : RepoImpl) : Prop :=
  ∀ (h : SkewHeap Int),
    impl.heap.skewHeapClear (impl.heap.skewHeapClear h) =
      impl.heap.skewHeapClear h

/-- After inserting a value, the visible top is either the inserted value or the old top
(insert can only change the top to the inserted value or leave it). -/
def spec_skewheap_insert_top (impl : RepoImpl) : Prop :=
  ∀ (h : SkewHeap Int) (v : Int) (oldTop newTop : Int),
    impl.heap.skewHeapTop h = some oldTop →
    impl.heap.skewHeapTop (impl.heap.skewHeapInsert h v) = some newTop →
    newTop = v ∨ newTop = oldTop

/-- After popping, any value still observed via `top` on the residual heap is no smaller
than the popped value. Requires `h` to satisfy the skew-heap min-heap-order invariant;
`pop` assumes (and preserves), but does not repair, this invariant. -/
def spec_skewheap_pop_next_top_ge_popped (impl : RepoImpl) : Prop :=
  ∀ (h : SkewHeap Int) (popped nextTop : Int),
    spec_helper_skew_is_min_heap h._root = true →
    (impl.heap.skewHeapPop h).1 = some popped →
    impl.heap.skewHeapTop (impl.heap.skewHeapPop h).2 = some nextTop →
    popped ≤ nextTop
