-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Heap.Impl.Heap

Polymorphic max-heap (list-backed). Translated from
`data_structures/heap/heap.py` in TheAlgorithms/Python.

The `Heap α` structure stores elements as a `List α` plus an explicit
`heap_size : Nat`. `heap_size` may be ≤ `h.length`; only the first
`heap_size` elements participate in heap invariants (this mirrors the
Python `heap_sort` which temporarily shrinks heap_size).

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
Implement only the function bodies.
-/

-- ── Core data types (DO NOT MODIFY) ──────────────────────────

/-- Polymorphic max-heap backed by a list and an explicit active size. -/
structure Heap (α : Type) where
  h : List α
  heap_size : Nat
  deriving Repr, BEq

namespace Heap

variable {α : Type}

-- ── API signatures (DO NOT MODIFY) ───────────────────────────
abbrev ParentIndexSig   := Heap α → Nat → Option Nat
abbrev LeftChildIdxSig  := Heap α → Nat → Option Nat
abbrev RightChildIdxSig := Heap α → Nat → Option Nat
abbrev BuildMaxHeapSig  [Ord α] := Heap α → List α → Heap α
-- @review human: Python's extract_max panics on empty heap; Lean returns Option.
abbrev ExtractMaxSig    [Ord α] := Heap α → Option (α × Heap α)
abbrev InsertSig        [Ord α] := Heap α → α → Heap α
abbrev HeapSortSig      [Ord α] := Heap α → Heap α

end Heap

-- !benchmark @start global_aux
-- Swap elements at positions i and j in a list (no-op if out of bounds).
-- Uses List.mapIdx — O(n) but avoids the `Inhabited` constraint.
private def heapListSwap {α : Type} (l : List α) (i j : Nat) : List α :=
  match l[i]?, l[j]? with
  | some vi, some vj =>
    l.mapIdx fun k x => if k == i then vj else if k == j then vi else x
  | _, _ => l

-- Sift-down one step on a List (max-heap).
-- fuel bounds recursion to heap height (≤ heap size).
private def maxHeapifyList {α : Type} [Ord α]
    (h : List α) (size : Nat) (index : Nat) (fuel : Nat) : List α :=
  match fuel with
  | 0 => h
  | fuel' + 1 =>
    let left  := 2 * index + 1
    let right := 2 * index + 2
    -- Find the index of the largest among h[index], h[left], h[right].
    let v := index
    let v := match h[left]?, h[v]? with
      | some lv, some vv => if left < size && Ord.compare lv vv == .gt then left else v
      | _, _ => v
    let v := match h[right]?, h[v]? with
      | some rv, some vv => if right < size && Ord.compare rv vv == .gt then right else v
      | _, _ => v
    if v != index then
      let h := heapListSwap h index v
      maxHeapifyList h size v fuel'
    else h

-- Apply max_heapify from index n down to 0 (for build_max_heap).
private def applyMaxHeapifyFrom {α : Type} [Ord α]
    (h : List α) (size : Nat) : Nat → List α
  | 0     => maxHeapifyList h size 0 size
  | n + 1 =>
    let h := maxHeapifyList h size (n + 1) size
    applyMaxHeapifyFrom h size n

-- Re-heapify from idx upward to root (for insert).
private def insertHelper {α : Type} [Ord α]
    (h : List α) (size : Nat) (idx : Nat) (fuel : Nat) : List α :=
  match fuel with
  | 0 => h
  | fuel' + 1 =>
    let h := maxHeapifyList h size idx size
    if idx == 0 then h
    else insertHelper h size ((idx - 1) / 2) fuel'

-- heap_sort inner loop: swap root with tail, then sift-down.
private def heapSortHelper {α : Type} [Ord α]
    (h : List α) : Nat → List α
  | 0     => h
  | j + 1 =>
    let h := heapListSwap h 0 (j + 1)
    let h := maxHeapifyList h (j + 1) 0 (j + 1)
    heapSortHelper h j
-- !benchmark @end global_aux

-- ── Implementation stubs ──────────────────────────────────────

-- !benchmark @start code_aux def=parent_index
-- !benchmark @end code_aux def=parent_index

def Heap.parent_index {α : Type} (self : Heap α) (child_idx : Nat) : Option Nat :=
-- !benchmark @start code def=parent_index
  if child_idx > 0 then some ((child_idx - 1) / 2) else none
-- !benchmark @end code def=parent_index

-- !benchmark @start code_aux def=left_child_idx
-- !benchmark @end code_aux def=left_child_idx

def Heap.left_child_idx {α : Type} (self : Heap α) (parent_idx : Nat) : Option Nat :=
-- !benchmark @start code def=left_child_idx
  let idx := 2 * parent_idx + 1
  if idx < self.heap_size then some idx else none
-- !benchmark @end code def=left_child_idx

-- !benchmark @start code_aux def=right_child_idx
-- !benchmark @end code_aux def=right_child_idx

def Heap.right_child_idx {α : Type} (self : Heap α) (parent_idx : Nat) : Option Nat :=
-- !benchmark @start code def=right_child_idx
  let idx := 2 * parent_idx + 2
  if idx < self.heap_size then some idx else none
-- !benchmark @end code def=right_child_idx

-- !benchmark @start code_aux def=build_max_heap
-- !benchmark @end code_aux def=build_max_heap

def Heap.build_max_heap {α : Type} [Ord α]
    (_self : Heap α) (collection : List α) : Heap α :=
-- !benchmark @start code def=build_max_heap
  let size := collection.length
  if size <= 1 then { h := collection, heap_size := size }
  else
    let startIdx := size / 2 - 1
    let h := applyMaxHeapifyFrom collection size startIdx
    { h := h, heap_size := size }
-- !benchmark @end code def=build_max_heap

-- !benchmark @start code_aux def=extract_max
-- !benchmark @end code_aux def=extract_max

-- @review human: Python panics on empty heap; Lean returns none.
def Heap.extract_max {α : Type} [Ord α] (self : Heap α) : Option (α × Heap α) :=
-- !benchmark @start code def=extract_max
  if self.heap_size == 0 then none
  else if self.heap_size == 1 then
    match self.h[0]? with
    | none   => none
    | some x => some (x, { h := [], heap_size := 0 })
  else
    -- Retrieve max element (h[0]) and last element (h[heap_size-1]).
    match self.h[0]?, self.h[self.heap_size - 1]? with
    | some maxElem, some lastElem =>
      -- Build new list: lastElem at front, remaining h[1..heap_size-2].
      let rest := (self.h.take (self.heap_size - 1)).tail
      let newH := lastElem :: rest
      let newH := maxHeapifyList newH (self.heap_size - 1) 0 (self.heap_size - 1)
      some (maxElem, { h := newH, heap_size := self.heap_size - 1 })
    | _, _ => none
-- !benchmark @end code def=extract_max

-- !benchmark @start code_aux def=insert
-- !benchmark @end code_aux def=insert

def Heap.insert {α : Type} [Ord α] (self : Heap α) (value : α) : Heap α :=
-- !benchmark @start code def=insert
  let h        := self.h ++ [value]
  let newSize  := self.heap_size + 1
  -- Parent index of the newly appended element (0-indexed at heap_size).
  let startIdx := if self.heap_size == 0 then 0 else (self.heap_size - 1) / 2
  -- fuel = startIdx + 1 so max_heapify runs from startIdx down to and INCLUDING the
  -- root (matching Python's `while idx >= 0` inclusive loop); a bare `startIdx`
  -- would drop the root-level heapify whenever startIdx = 0.
  let h        := insertHelper h newSize startIdx (startIdx + 1)
  { h := h, heap_size := newSize }
-- !benchmark @end code def=insert

-- !benchmark @start code_aux def=heap_sort
-- !benchmark @end code_aux def=heap_sort

def Heap.heap_sort {α : Type} [Ord α] (self : Heap α) : Heap α :=
-- !benchmark @start code def=heap_sort
  if self.heap_size <= 1 then self
  else
    let h := heapSortHelper self.h (self.heap_size - 1)
    { h := h, heap_size := self.heap_size }
-- !benchmark @end code def=heap_sort
