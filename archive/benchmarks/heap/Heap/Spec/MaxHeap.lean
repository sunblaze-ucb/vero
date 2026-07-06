import Heap.Harness

/-!
# Heap.Spec.MaxHeap

Specifications for the integer max-heap (MaxHeap.lean). Each `spec_*` is a property over an
arbitrary `impl : RepoImpl`.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- Count occurrences of an integer in a list. -/
def spec_helper_binary_countInt (x : Int) : List Int → Nat
  | [] => 0
  | y :: ys => (if x == y then 1 else 0) + spec_helper_binary_countInt x ys

/-- `get_list` returns the internal `data` list exactly. -/
def spec_get_list_is_data (impl : RepoImpl) : Prop :=
  ∀ (h : BinaryHeap),
    impl.heap.binaryHeapGetList h = h.data

/-- `size` returns `data.length`. -/
def spec_size_is_length (impl : RepoImpl) : Prop :=
  ∀ (h : BinaryHeap),
    impl.heap.binaryHeapSize h = h.data.length

/-- `size h` equals the length of `get_list h`. -/
def spec_size_via_get_list (impl : RepoImpl) : Prop :=
  ∀ (h : BinaryHeap),
    impl.heap.binaryHeapSize h = (impl.heap.binaryHeapGetList h).length

/-- Inserting any value increases `size` by exactly 1. -/
def spec_maxheap_insert_size_grows (impl : RepoImpl) : Prop :=
  ∀ (h : BinaryHeap) (v : Int),
    impl.heap.binaryHeapSize (impl.heap.binaryHeapInsert h v)
      = impl.heap.binaryHeapSize h + 1

/-- Inserting into an empty `BinaryHeap` yields `data = [v]`. -/
def spec_maxheap_insert_into_empty_root (impl : RepoImpl) : Prop :=
  ∀ (v : Int),
    impl.heap.binaryHeapGetList (impl.heap.binaryHeapInsert { data := [] } v) = [v]

/-- Inserting 6 then 10 into an empty heap places 10 at position 0 (the root). -/
def spec_maxheap_insert_max_at_root_concrete (impl : RepoImpl) : Prop :=
  (impl.heap.binaryHeapGetList
    (impl.heap.binaryHeapInsert
      (impl.heap.binaryHeapInsert { data := [] } 6) 10))[0]?
  = some 10

/-- After inserting 6, 10, 15, 12, `pop` returns 15 (the maximum). -/
def spec_maxheap_pop_returns_max_concrete (impl : RepoImpl) : Prop :=
  let h0 := impl.heap.binaryHeapInsert { data := [] } 6
  let h1 := impl.heap.binaryHeapInsert h0 10
  let h2 := impl.heap.binaryHeapInsert h1 15
  let h3 := impl.heap.binaryHeapInsert h2 12
  (impl.heap.binaryHeapPop h3).1 = 15

/-- Popping from a single-element heap returns the inserted value and leaves size 0. -/
def spec_maxheap_pop_singleton_concrete (impl : RepoImpl) : Prop :=
  let (v, h') := impl.heap.binaryHeapPop
    (impl.heap.binaryHeapInsert { data := [] } 99)
  v = 99 ∧ impl.heap.binaryHeapSize h' = 0

/-- On any non-empty `BinaryHeap`, `pop` produces a heap whose size is exactly one less. -/
def spec_maxheap_pop_size_shrinks (impl : RepoImpl) : Prop :=
  ∀ (h : BinaryHeap),
    ¬ h.data.isEmpty →
    (impl.heap.binaryHeapPop h).2.data.length = h.data.length - 1

/-- When `get_list h` exposes a head value `head`, `pop h` returns that head value. -/
def spec_maxheap_pop_returns_list_head (impl : RepoImpl) : Prop :=
  ∀ (h : BinaryHeap) (head : Int) (tail : List Int),
    impl.heap.binaryHeapGetList h = head :: tail →
    (impl.heap.binaryHeapPop h).1 = head

/-- After inserting a value into any `BinaryHeap`, the value is observable in the public
`get_list` view. -/
def spec_maxheap_insert_get_list_contains (impl : RepoImpl) : Prop :=
  ∀ (h : BinaryHeap) (v : Int),
    v ∈ impl.heap.binaryHeapGetList (impl.heap.binaryHeapInsert h v)

/-- Insert preserves all old elements and adds exactly one copy of the inserted value. -/
def spec_maxheap_insert_preserves_multiset (impl : RepoImpl) : Prop :=
  ∀ (h : BinaryHeap) (v x : Int),
    spec_helper_binary_countInt x
      (impl.heap.binaryHeapGetList (impl.heap.binaryHeapInsert h v)) =
      spec_helper_binary_countInt x (impl.heap.binaryHeapGetList h) +
        if x == v then 1 else 0
