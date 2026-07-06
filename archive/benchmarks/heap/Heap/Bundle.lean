import Heap.Impl.Heap
import Heap.Impl.MaxHeap
import Heap.Impl.MinHeap
import Heap.Impl.BinomialHeap
import Heap.Impl.SkewHeap
import Heap.Impl.RandomizedHeap
import Heap.Impl.HeapGeneric

/-!
# Heap.Bundle

Per-package implementation bundle for the `Heap` root package.
Collects all API signatures into one structure — one field per API.
Polymorphic binders are expanded inline.

DO NOT MODIFY — benchmark infrastructure.
-/

structure HeapBundle where
  -- ── Heap (polymorphic max-heap, heap.py) ─────────────────
  heapParentIndex   : ∀ {α : Type}, Heap α → Nat → Option Nat
  heapLeftChildIdx  : ∀ {α : Type}, Heap α → Nat → Option Nat
  heapRightChildIdx : ∀ {α : Type}, Heap α → Nat → Option Nat
  heapBuildMaxHeap  : ∀ {α : Type} [Ord α], Heap α → List α → Heap α
  heapExtractMax    : ∀ {α : Type} [Ord α], Heap α → Option (α × Heap α)
  heapInsert        : ∀ {α : Type} [Ord α], Heap α → α → Heap α
  heapHeapSort      : ∀ {α : Type} [Ord α], Heap α → Heap α
  -- ── BinaryHeap (max_heap.py) ──────────────────────────────
  binaryHeapInsert  : BinaryHeap → Int → BinaryHeap
  binaryHeapPop     : BinaryHeap → Int × BinaryHeap
  binaryHeapGetList : BinaryHeap → List Int
  binaryHeapSize    : BinaryHeap → Nat
  -- ── MinHeap (min_heap.py) ────────────────────────────────
  minHeapGetParentIdx    : MinHeap → Int → Int
  minHeapGetLeftChildIdx : MinHeap → Int → Int
  minHeapGetRightChildIdx: MinHeap → Int → Int
  minHeapIsEmpty         : MinHeap → Bool
  -- ── BinomialHeap (binomial_heap.py) ──────────────────────
  binomialHeapInsert    : BinomialHeap → Int → BinomialHeap
  binomialHeapPeek      : BinomialHeap → Int
  binomialHeapIsEmpty   : BinomialHeap → Bool
  binomialHeapDeleteMin : BinomialHeap → Int × BinomialHeap
  -- ── SkewHeap (skew_heap.py) ──────────────────────────────
  skewHeapInsert : ∀ {α : Type} [Ord α], SkewHeap α → α → SkewHeap α
  skewHeapTop    : ∀ {α : Type} [Ord α], SkewHeap α → Option α
  skewHeapPop    : ∀ {α : Type} [Ord α], SkewHeap α → Option α × SkewHeap α
  skewHeapClear  : ∀ {α : Type}, SkewHeap α → SkewHeap α
  -- ── RandomizedHeap (randomized_heap.py) ──────────────────
  randomizedHeapInsert       : ∀ {α : Type} [Ord α], RandomizedHeap α → α → RandomizedHeap α
  randomizedHeapTop          : ∀ {α : Type} [Ord α], RandomizedHeap α → Option α
  randomizedHeapToSortedList : ∀ {α : Type} [Ord α], RandomizedHeap α → List α
  randomizedHeapClear        : ∀ {α : Type}, RandomizedHeap α → RandomizedHeap α
  -- ── GenericHeap (heap_generic.py) ────────────────────────
  genericHeapInsertItem  : GenericHeap → Int → Int → GenericHeap
  genericHeapGetTop      : GenericHeap → Option (List Int)
  genericHeapDeleteItem  : GenericHeap → Int → GenericHeap
  genericHeapExtractTop  : GenericHeap → Option (List Int) × GenericHeap
  genericHeapUpdateItem  : GenericHeap → Int → Int → GenericHeap
