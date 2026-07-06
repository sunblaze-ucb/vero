import Heap.Bundle

/-!
# Heap.Harness

Benchmark harness: `RepoImpl` structure (one field for the `Heap` package),
`canonical` instance wiring all reference implementations, and the
`joint_unsat` macro.

DO NOT MODIFY — benchmark infrastructure.
-/

structure RepoImpl where
  heap : HeapBundle

def canonical : RepoImpl where
  heap := {
    heapParentIndex   := Heap.parent_index
    heapLeftChildIdx  := Heap.left_child_idx
    heapRightChildIdx := Heap.right_child_idx
    heapBuildMaxHeap  := Heap.build_max_heap
    heapExtractMax    := Heap.extract_max
    heapInsert        := Heap.insert
    heapHeapSort      := Heap.heap_sort
    binaryHeapInsert  := BinaryHeap.insert
    binaryHeapPop     := BinaryHeap.pop
    binaryHeapGetList := BinaryHeap.get_list
    binaryHeapSize    := BinaryHeap.size
    minHeapGetParentIdx     := MinHeap.get_parent_idx
    minHeapGetLeftChildIdx  := MinHeap.get_left_child_idx
    minHeapGetRightChildIdx := MinHeap.get_right_child_idx
    minHeapIsEmpty          := MinHeap.is_empty
    binomialHeapInsert    := BinomialHeap.insert
    binomialHeapPeek      := BinomialHeap.peek
    binomialHeapIsEmpty   := BinomialHeap.is_empty
    binomialHeapDeleteMin := BinomialHeap.delete_min
    skewHeapInsert := SkewHeap.insert
    skewHeapTop    := SkewHeap.top
    skewHeapPop    := SkewHeap.pop
    skewHeapClear  := SkewHeap.clear
    randomizedHeapInsert       := RandomizedHeap.insert
    randomizedHeapTop          := RandomizedHeap.top
    randomizedHeapToSortedList := RandomizedHeap.to_sorted_list
    randomizedHeapClear        := RandomizedHeap.clear
    genericHeapInsertItem  := GenericHeap.insert_item
    genericHeapGetTop      := GenericHeap.get_top
    genericHeapDeleteItem  := GenericHeap.delete_item
    genericHeapExtractTop  := GenericHeap.extract_top
    genericHeapUpdateItem  := GenericHeap.update_item
  }

/-- `joint_unsat spec_A spec_B [spec_C …] by <proof>` generates the
    ∧-conjunction unsat theorem. Variadic; no sort / no dedup — anti-cheat
    is enforced at `!solution` extraction during evaluation. -/
syntax "joint_unsat" ident ident ident* "by" tacticSeq : command

open Lean in
macro_rules
  | `(joint_unsat $s1 $s2 $[$rest]* by $proof) => do
    let specs := #[s1, s2] ++ rest
    let name := specs.foldl (init := `joint_unsat) fun acc s => Name.append acc s.getId
    let mut body ← `($(specs[0]!) impl)
    for s in specs[1:] do
      body ← `($body ∧ $s impl)
    `(theorem $(mkIdent name) : ¬ ∃ impl : RepoImpl, $body := by $proof)
