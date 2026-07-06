import Heap.Impl.Heap
import Heap.Impl.MaxHeap
import Heap.Impl.MinHeap
import Heap.Impl.BinomialHeap
import Heap.Impl.SkewHeap
import Heap.Impl.RandomizedHeap
import Heap.Impl.HeapGeneric
import Heap.Bundle
import Heap.Harness

/-!
# Heap.Test

`#guard` conformance tests. Every guard dispatches through `canonical.heap.*`
so the harness wiring is exercised end-to-end. Coverage target: ≥3 guards
per API (empty / typical / edge — duplicates / multi-element when sensible).

Pre-agent-gen replaces marker content in `Impl/*.lean` with `sorry`; these
guards catch regressions in the reference impls.

DO NOT MODIFY — infrastructure.
-/

-- ── Heap (heap.py) ───────────────────────────────────────────

-- parent_index: child 1 (0-indexed) → 0.
#guard canonical.heap.heapParentIndex (α := Int) { h := [], heap_size := 0 } 1 == some 0

-- parent_index: child 3 → 1.
#guard canonical.heap.heapParentIndex (α := Int) { h := [], heap_size := 0 } 3 == some 1

-- parent_index: root has no parent.
#guard canonical.heap.heapParentIndex (α := Int) { h := [], heap_size := 0 } 0 == none

-- parent_index: child 6 → 2.
#guard canonical.heap.heapParentIndex (α := Int) { h := [], heap_size := 0 } 6 == some 2

-- left_child_idx: parent 0, heap_size 3 → some 1.
#guard canonical.heap.heapLeftChildIdx (α := Int) { h := [], heap_size := 3 } 0 == some 1

-- left_child_idx: parent 1, heap_size 5 → some 3.
#guard canonical.heap.heapLeftChildIdx (α := Int) { h := [], heap_size := 5 } 1 == some 3

-- left_child_idx: out-of-range parent on empty heap → none.
#guard canonical.heap.heapLeftChildIdx (α := Int) { h := [], heap_size := 0 } 0 == none

-- right_child_idx: parent 0, heap_size 3 → some 2.
#guard canonical.heap.heapRightChildIdx (α := Int) { h := [], heap_size := 3 } 0 == some 2

-- right_child_idx: parent 2, heap_size 3 → none (out of range).
#guard canonical.heap.heapRightChildIdx (α := Int) { h := [], heap_size := 3 } 2 == none

-- right_child_idx: parent 1, heap_size 5 → some 4.
#guard canonical.heap.heapRightChildIdx (α := Int) { h := [], heap_size := 5 } 1 == some 4

-- build_max_heap: empty input.
#guard
  (canonical.heap.heapBuildMaxHeap (α := Int) { h := [], heap_size := 0 } []).h == []

-- build_max_heap: single element.
#guard
  (canonical.heap.heapBuildMaxHeap (α := Int) { h := [], heap_size := 0 } [42]).h == [42]

-- build_max_heap: max element ends up at the root.
#guard
  (canonical.heap.heapBuildMaxHeap (α := Int) { h := [], heap_size := 0 }
    [103, 9, 1, 7, 11, 15, 25, 201, 209, 107, 5]).h[0]?
  == some 209

-- build_max_heap: full layout.
#guard
  (canonical.heap.heapBuildMaxHeap (α := Int) { h := [], heap_size := 0 }
    [103, 9, 1, 7, 11, 15, 25, 201, 209, 107, 5]).h
  == [209, 201, 25, 103, 107, 15, 1, 9, 7, 11, 5]

-- extract_max: empty heap → none.
#guard
  (canonical.heap.heapExtractMax (α := Int) { h := [], heap_size := 0 }) == none

-- extract_max: returns the maximum element.
#guard
  (canonical.heap.heapExtractMax (α := Int)
    { h := [209, 201, 25, 103, 107, 15, 1, 9, 7, 11, 5], heap_size := 11 }).map Prod.fst
  == some 209

-- extract_max: heap_size shrinks by 1.
#guard
  ((canonical.heap.heapExtractMax (α := Int)
    { h := [209, 201, 25, 103, 107, 15, 1, 9, 7, 11, 5], heap_size := 11 }).map
      (fun p => p.2.heap_size)) == some 10

-- insert: heap_size grows by 1.
#guard
  (canonical.heap.heapInsert (α := Int)
    { h := [201, 107, 25, 103, 11, 15, 1, 9, 7, 5], heap_size := 10 } 100).heap_size
  == 11

-- insert: into empty heap.
#guard
  (canonical.heap.heapInsert (α := Int) { h := [], heap_size := 0 } 7).h == [7]

-- insert: with duplicate values keeps size growth correct.
#guard
  (canonical.heap.heapInsert (α := Int)
    (canonical.heap.heapInsert (α := Int) { h := [], heap_size := 0 } 5) 5).heap_size == 2

-- heap_sort: ascending order on a populated heap.
#guard
  (canonical.heap.heapHeapSort (α := Int)
    { h := [209, 201, 25, 103, 107, 15, 1, 9, 7, 11, 5], heap_size := 11 }).h
  == [1, 5, 7, 9, 11, 15, 25, 103, 107, 201, 209]

-- heap_sort: empty heap is unchanged.
#guard
  (canonical.heap.heapHeapSort (α := Int) { h := [], heap_size := 0 }).h == []

-- heap_sort: single-element heap is unchanged.
#guard
  (canonical.heap.heapHeapSort (α := Int) { h := [42], heap_size := 1 }).h == [42]

-- ── BinaryHeap (max_heap.py) ─────────────────────────────────

-- insert: empty heap → size 1.
#guard (canonical.heap.binaryHeapInsert { data := [] } 6).size == 1

-- insert: builds list with the new value at the root after sift-up.
#guard (canonical.heap.binaryHeapInsert { data := [] } 6).get_list == [6]

-- insert: inserting a larger value sifts to the root.
#guard
  (canonical.heap.binaryHeapInsert
    (canonical.heap.binaryHeapInsert { data := [] } 6) 10).get_list[0]? == some 10

-- pop: returns the max (15) after inserting 6,10,15,12.
#guard
  let h0 := canonical.heap.binaryHeapInsert { data := [] } 6
  let h1 := canonical.heap.binaryHeapInsert h0 10
  let h2 := canonical.heap.binaryHeapInsert h1 15
  let h3 := canonical.heap.binaryHeapInsert h2 12
  match canonical.heap.binaryHeapPop h3 with
  | (v, _) => v == 15

-- pop: second pop returns 12.
#guard
  let h0 := canonical.heap.binaryHeapInsert { data := [] } 6
  let h1 := canonical.heap.binaryHeapInsert h0 10
  let h2 := canonical.heap.binaryHeapInsert h1 15
  let h3 := canonical.heap.binaryHeapInsert h2 12
  match canonical.heap.binaryHeapPop h3 with
  | (_, h) => match canonical.heap.binaryHeapPop h with
    | (v, _) => v == 12

-- pop: pop on a single-element heap leaves it empty.
#guard
  match canonical.heap.binaryHeapPop
      (canonical.heap.binaryHeapInsert { data := [] } 99) with
  | (v, h) => v == 99 && canonical.heap.binaryHeapSize h == 0

-- get_list: returns all elements.
#guard canonical.heap.binaryHeapGetList { data := [3, 2, 1] } == [3, 2, 1]

-- get_list: empty heap → empty list.
#guard canonical.heap.binaryHeapGetList { data := [] } == []

-- get_list: matches insertion result.
#guard canonical.heap.binaryHeapGetList
  (canonical.heap.binaryHeapInsert { data := [] } 6) == [6]

-- size: empty heap.
#guard canonical.heap.binaryHeapSize { data := [] } == 0

-- size: after a single insert.
#guard
  canonical.heap.binaryHeapSize
    (canonical.heap.binaryHeapInsert { data := [] } 6) == 1

-- size: after one pop on a four-element heap.
#guard
  let h0 := canonical.heap.binaryHeapInsert { data := [] } 6
  let h1 := canonical.heap.binaryHeapInsert h0 10
  let h2 := canonical.heap.binaryHeapInsert h1 15
  let h3 := canonical.heap.binaryHeapInsert h2 12
  match canonical.heap.binaryHeapPop h3 with
  | (_, h) => canonical.heap.binaryHeapSize h == 3

-- ── MinHeap (min_heap.py) — only index/empty functions exposed ─────

-- get_parent_idx: idx 0 → -1 (Python (0-1)//2).
#guard canonical.heap.minHeapGetParentIdx { heap := [], idxOf := [], heapDict := [] } 0 == -1

-- get_parent_idx: idx 1 → 0.
#guard canonical.heap.minHeapGetParentIdx { heap := [], idxOf := [], heapDict := [] } 1 == 0

-- get_parent_idx: idx 2 → 0.
#guard canonical.heap.minHeapGetParentIdx { heap := [], idxOf := [], heapDict := [] } 2 == 0

-- get_left_child_idx: idx 0 → 1.
#guard canonical.heap.minHeapGetLeftChildIdx { heap := [], idxOf := [], heapDict := [] } 0 == 1

-- get_left_child_idx: idx 1 → 3.
#guard canonical.heap.minHeapGetLeftChildIdx { heap := [], idxOf := [], heapDict := [] } 1 == 3

-- get_left_child_idx: idx 5 → 11.
#guard canonical.heap.minHeapGetLeftChildIdx { heap := [], idxOf := [], heapDict := [] } 5 == 11

-- get_right_child_idx: idx 0 → 2.
#guard canonical.heap.minHeapGetRightChildIdx { heap := [], idxOf := [], heapDict := [] } 0 == 2

-- get_right_child_idx: idx 1 → 4.
#guard canonical.heap.minHeapGetRightChildIdx { heap := [], idxOf := [], heapDict := [] } 1 == 4

-- get_right_child_idx: idx 5 → 12.
#guard canonical.heap.minHeapGetRightChildIdx { heap := [], idxOf := [], heapDict := [] } 5 == 12

-- is_empty: empty heap → true.
#guard canonical.heap.minHeapIsEmpty { heap := [], idxOf := [], heapDict := [] } == true

-- is_empty: non-empty heap → false.
#guard
  canonical.heap.minHeapIsEmpty
    { heap := [{ name := "a", val := 1 }], idxOf := [("a", 0)], heapDict := [("a", 1)] }
  == false

-- is_empty: another non-empty heap → false.
#guard
  canonical.heap.minHeapIsEmpty
    { heap := [{ name := "x", val := 0 }, { name := "y", val := 5 }],
      idxOf := [("x", 0), ("y", 1)], heapDict := [("x", 0), ("y", 5)] }
  == false

-- ── BinomialHeap (binomial_heap.py) ──────────────────────────

-- insert: empty heap becomes non-empty.
#guard
  canonical.heap.binomialHeapIsEmpty
    (canonical.heap.binomialHeapInsert { heap := [] } 5) == false

-- insert: peek of single-element heap is the inserted value.
#guard
  canonical.heap.binomialHeapPeek
    (canonical.heap.binomialHeapInsert { heap := [] } 5) == 5

-- insert: peek after multiple inserts is the smallest value.
#guard
  canonical.heap.binomialHeapPeek
    ((canonical.heap.binomialHeapInsert
      (canonical.heap.binomialHeapInsert
        (canonical.heap.binomialHeapInsert { heap := [] } 10) 3) 7)) == 3

-- peek: smallest of three inserted values.
#guard
  canonical.heap.binomialHeapPeek
    ((canonical.heap.binomialHeapInsert
      (canonical.heap.binomialHeapInsert
        (canonical.heap.binomialHeapInsert { heap := [] } 10) 3) 7)) == 3

-- peek: single element.
#guard
  canonical.heap.binomialHeapPeek
    (canonical.heap.binomialHeapInsert { heap := [] } 42) == 42

-- peek: with duplicate priorities, the smallest still wins.
#guard
  canonical.heap.binomialHeapPeek
    ((canonical.heap.binomialHeapInsert
      (canonical.heap.binomialHeapInsert
        (canonical.heap.binomialHeapInsert { heap := [] } 4) 4) 4)) == 4

-- is_empty: fresh heap is empty.
#guard canonical.heap.binomialHeapIsEmpty { heap := [] } == true

-- is_empty: after insert, not empty.
#guard
  canonical.heap.binomialHeapIsEmpty
    (canonical.heap.binomialHeapInsert { heap := [] } 5) == false

-- is_empty: after multiple inserts, not empty.
#guard
  canonical.heap.binomialHeapIsEmpty
    ((canonical.heap.binomialHeapInsert
      (canonical.heap.binomialHeapInsert { heap := [] } 1) 2)) == false

-- delete_min: returns smallest value 3.
#guard
  match canonical.heap.binomialHeapDeleteMin
      ((canonical.heap.binomialHeapInsert
        (canonical.heap.binomialHeapInsert
          (canonical.heap.binomialHeapInsert { heap := [] } 10) 3) 7)) with
  | (v, _) => v == 3

-- delete_min: shrinks the heap by one element.
#guard
  match canonical.heap.binomialHeapDeleteMin
      ((canonical.heap.binomialHeapInsert
        (canonical.heap.binomialHeapInsert
          (canonical.heap.binomialHeapInsert { heap := [] } 10) 3) 7)) with
  | (_, h) => h.heap.length == 2

-- delete_min: on a single-element heap leaves it empty.
#guard
  match canonical.heap.binomialHeapDeleteMin
      (canonical.heap.binomialHeapInsert { heap := [] } 99) with
  | (v, h) => v == 99 && canonical.heap.binomialHeapIsEmpty h == true

-- ── SkewHeap (skew_heap.py) ──────────────────────────────────

-- insert: empty heap, top of result is the inserted value.
#guard
  canonical.heap.skewHeapTop
    (canonical.heap.skewHeapInsert (α := Int) { _root := none } 5) == some 5

-- insert: smaller of two inserts wins as top.
#guard
  canonical.heap.skewHeapTop
    (canonical.heap.skewHeapInsert
      (canonical.heap.skewHeapInsert (α := Int) { _root := none } 5) 3)
  == some 3

-- insert: with duplicate priorities, top is one of them.
#guard
  canonical.heap.skewHeapTop
    (canonical.heap.skewHeapInsert
      (canonical.heap.skewHeapInsert (α := Int) { _root := none } 7) 7)
  == some 7

-- top: empty heap → none.
#guard canonical.heap.skewHeapTop (α := Int) { _root := none } == none

-- top: with String elements (polymorphic).
#guard
  canonical.heap.skewHeapTop
    (canonical.heap.skewHeapInsert (α := String) { _root := none } "hello") == some "hello"

-- top: smallest of three insertions.
#guard
  canonical.heap.skewHeapTop
    (canonical.heap.skewHeapInsert
      (canonical.heap.skewHeapInsert
        (canonical.heap.skewHeapInsert (α := Int) { _root := none } 5) 3) 7)
  == some 3

-- pop: returns the top element.
#guard
  match canonical.heap.skewHeapPop
      (canonical.heap.skewHeapInsert
        (canonical.heap.skewHeapInsert (α := Int) { _root := none } 5) 3) with
  | (v, _) => v == some 3

-- pop: on empty heap returns none and the heap stays empty.
#guard
  match canonical.heap.skewHeapPop (α := Int) { _root := none } with
  | (v, h) => v == none && canonical.heap.skewHeapTop h == none

-- pop: after pop the second-smallest becomes the top.
#guard
  match canonical.heap.skewHeapPop
      (canonical.heap.skewHeapInsert
        (canonical.heap.skewHeapInsert (α := Int) { _root := none } 5) 3) with
  | (_, h) => canonical.heap.skewHeapTop h == some 5

-- clear: clearing makes the heap empty.
#guard
  canonical.heap.skewHeapTop
    (canonical.heap.skewHeapClear
      (canonical.heap.skewHeapInsert (α := Int) { _root := none } 5)) == none

-- clear: clearing an already-empty heap is still empty.
#guard
  canonical.heap.skewHeapTop (α := Int)
    (canonical.heap.skewHeapClear (α := Int) { _root := none }) == none

-- clear: clearing a multi-element heap empties it.
#guard
  canonical.heap.skewHeapTop
    (canonical.heap.skewHeapClear
      (canonical.heap.skewHeapInsert
        (canonical.heap.skewHeapInsert
          (canonical.heap.skewHeapInsert (α := Int) { _root := none } 5) 3) 7)) == none

-- ── RandomizedHeap (randomized_heap.py) ──────────────────────

-- insert: top of single-element heap is the inserted value.
#guard
  canonical.heap.randomizedHeapTop
    (canonical.heap.randomizedHeapInsert (α := Int) { _root := none } 5) == some 5

-- insert: smaller of two inserts wins as top.
#guard
  canonical.heap.randomizedHeapTop
    (canonical.heap.randomizedHeapInsert
      (canonical.heap.randomizedHeapInsert (α := Int) { _root := none } 5) 3)
  == some 3

-- insert: with duplicate priorities, top is one of them.
#guard
  canonical.heap.randomizedHeapTop
    (canonical.heap.randomizedHeapInsert
      (canonical.heap.randomizedHeapInsert (α := Int) { _root := none } 4) 4)
  == some 4

-- top: empty heap → none.
#guard canonical.heap.randomizedHeapTop (α := Int) { _root := none } == none

-- top: with Nat elements (polymorphic).
#guard
  canonical.heap.randomizedHeapTop
    (canonical.heap.randomizedHeapInsert (α := Nat) { _root := none } 7) == some 7

-- top: smallest of three insertions.
#guard
  canonical.heap.randomizedHeapTop
    (canonical.heap.randomizedHeapInsert
      (canonical.heap.randomizedHeapInsert
        (canonical.heap.randomizedHeapInsert (α := Int) { _root := none } 5) 3) 7)
  == some 3

-- to_sorted_list: ascending order on three insertions.
#guard
  canonical.heap.randomizedHeapToSortedList
    (canonical.heap.randomizedHeapInsert
      (canonical.heap.randomizedHeapInsert
        (canonical.heap.randomizedHeapInsert (α := Int) { _root := none } 5) 3) 7)
  == [3, 5, 7]

-- to_sorted_list: empty heap → [].
#guard canonical.heap.randomizedHeapToSortedList (α := Int) { _root := none } == []

-- to_sorted_list: single element.
#guard
  canonical.heap.randomizedHeapToSortedList
    (canonical.heap.randomizedHeapInsert (α := Int) { _root := none } 42) == [42]

-- clear: clearing makes the heap empty.
#guard
  canonical.heap.randomizedHeapTop
    (canonical.heap.randomizedHeapClear
      (canonical.heap.randomizedHeapInsert (α := Int) { _root := none } 5)) == none

-- clear: clearing an already-empty heap stays empty.
#guard
  canonical.heap.randomizedHeapTop (α := Int)
    (canonical.heap.randomizedHeapClear (α := Int) { _root := none }) == none

-- clear: clearing a multi-element heap empties it.
#guard
  canonical.heap.randomizedHeapTop
    (canonical.heap.randomizedHeapClear
      (canonical.heap.randomizedHeapInsert
        (canonical.heap.randomizedHeapInsert
          (canonical.heap.randomizedHeapInsert (α := Int) { _root := none } 5) 3) 7)) == none

-- ── GenericHeap (heap_generic.py) ────────────────────────────

-- insert_item: empty heap becomes size 1.
#guard
  (canonical.heap.genericHeapInsertItem
    { arr := [], posMap := [], size := 0 } 1 10).size == 1

-- insert_item: two inserts produce size 2.
#guard
  (canonical.heap.genericHeapInsertItem
    (canonical.heap.genericHeapInsertItem
      { arr := [], posMap := [], size := 0 } 1 10) 2 20).size == 2

-- insert_item: top of a single-element heap is the inserted [item, key].
#guard
  canonical.heap.genericHeapGetTop
    (canonical.heap.genericHeapInsertItem
      { arr := [], posMap := [], size := 0 } 42 100) == some [42, 100]

-- get_top: empty heap → none.
#guard canonical.heap.genericHeapGetTop { arr := [], posMap := [], size := 0 } == none

-- get_top: single-item heap returns the only entry.
#guard
  canonical.heap.genericHeapGetTop
    (canonical.heap.genericHeapInsertItem
      { arr := [], posMap := [], size := 0 } 1 10) == some [1, 10]

-- get_top: with two items, larger key bubbles to the top (max-heap by key).
#guard
  canonical.heap.genericHeapGetTop
    (canonical.heap.genericHeapInsertItem
      (canonical.heap.genericHeapInsertItem
        { arr := [], posMap := [], size := 0 } 1 10) 2 20) == some [2, 20]

-- delete_item: removing the only item makes size 0.
#guard
  (canonical.heap.genericHeapDeleteItem
    (canonical.heap.genericHeapInsertItem
      { arr := [], posMap := [], size := 0 } 1 10) 1).size == 0

-- delete_item: removing a missing item is a no-op.
#guard
  (canonical.heap.genericHeapDeleteItem
    (canonical.heap.genericHeapInsertItem
      { arr := [], posMap := [], size := 0 } 1 10) 999).size == 1

-- delete_item: after deletion, get_top returns none.
#guard
  canonical.heap.genericHeapGetTop
    (canonical.heap.genericHeapDeleteItem
      (canonical.heap.genericHeapInsertItem
        { arr := [], posMap := [], size := 0 } 1 10) 1) == none

-- extract_top: returns top entry and shrinks heap.
#guard
  match canonical.heap.genericHeapExtractTop
      (canonical.heap.genericHeapInsertItem
        { arr := [], posMap := [], size := 0 } 42 100) with
  | (top, h) => top == some [42, 100] && h.size == 0

-- extract_top: on an empty heap → (none, self).
#guard
  match canonical.heap.genericHeapExtractTop
      { arr := [], posMap := [], size := 0 } with
  | (top, h) => top == none && h.size == 0

-- extract_top: on a two-item heap, top is the one with the larger key.
#guard
  match canonical.heap.genericHeapExtractTop
      (canonical.heap.genericHeapInsertItem
        (canonical.heap.genericHeapInsertItem
          { arr := [], posMap := [], size := 0 } 1 10) 2 20) with
  | (top, h) => top == some [2, 20] && h.size == 1

-- update_item: updating a missing item is a no-op (size unchanged).
#guard
  (canonical.heap.genericHeapUpdateItem
    (canonical.heap.genericHeapInsertItem
      { arr := [], posMap := [], size := 0 } 1 10) 999 50).size == 1

-- update_item: updating an item changes its key in get_top (single item).
#guard
  canonical.heap.genericHeapGetTop
    (canonical.heap.genericHeapUpdateItem
      (canonical.heap.genericHeapInsertItem
        { arr := [], posMap := [], size := 0 } 1 10) 1 50) == some [1, 50]

-- update_item: increasing a key promotes the item to the top.
#guard
  canonical.heap.genericHeapGetTop
    (canonical.heap.genericHeapUpdateItem
      (canonical.heap.genericHeapInsertItem
        (canonical.heap.genericHeapInsertItem
          { arr := [], posMap := [], size := 0 } 1 10) 2 20) 1 999) == some [1, 999]
