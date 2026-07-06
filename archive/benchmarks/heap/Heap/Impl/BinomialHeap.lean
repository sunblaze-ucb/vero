-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Heap.Impl.BinomialHeap

Integer binomial min-heap. Translated from
`data_structures/heap/binomial_heap.py` in TheAlgorithms/Python.

The Python source contains "Merge logic..." and "Delete logic..." stubs (the
actual merge/delete code is omitted). This Lean translation implements the
four exposed APIs (`insert`, `peek`, `is_empty`, `delete_min`) using a
0-indexed array-backed min-heap, which has the same observable behaviour.

`peek` and `delete_min` panic on an empty heap (matching Python's
`AttributeError` on `self.min_node.val` when the heap is empty).

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
Implement only the function bodies.
-/

-- ── Core data type (DO NOT MODIFY) ───────────────────────────

/-- Integer binomial min-heap (array-backed in this translation). -/
structure BinomialHeap where
  heap : List Int   -- 0-indexed min-heap array
  deriving Repr, BEq, Inhabited

namespace BinomialHeap

-- ── API signatures (DO NOT MODIFY) ───────────────────────────
abbrev InsertSig    := BinomialHeap → Int → BinomialHeap
abbrev PeekSig      := BinomialHeap → Int
abbrev IsEmptySig   := BinomialHeap → Bool
-- @review human: Python panics on empty heap; Int Inhabited allows panic!
abbrev DeleteMinSig := BinomialHeap → Int × BinomialHeap

end BinomialHeap

-- !benchmark @start global_aux
-- Swap elements at positions i and j (no-op if out of bounds).
private def bmSwap (l : List Int) (i j : Nat) : List Int :=
  match l[i]?, l[j]? with
  | some vi, some vj =>
    l.mapIdx fun k x => if k == i then vj else if k == j then vi else x
  | _, _ => l

-- Sift element at position i upward (min-heap).
private def bmSiftUp (data : List Int) (i : Nat) (fuel : Nat) : List Int :=
  match fuel with
  | 0      => data
  | f' + 1 =>
    if i == 0 then data
    else
      let p := (i - 1) / 2
      match data[i]?, data[p]? with
      | some vi, some vp =>
        if vi < vp then bmSiftUp (bmSwap data i p) p f'
        else data
      | _, _ => data

-- Sift element at position i downward (min-heap).
private def bmSiftDown (data : List Int) (size : Nat) (i : Nat) (fuel : Nat) : List Int :=
  match fuel with
  | 0      => data
  | f' + 1 =>
    let left  := 2 * i + 1
    let right := 2 * i + 2
    if left >= size then data
    else
      let smaller :=
        if right >= size then left
        else match data[left]?, data[right]? with
          | some lv, some rv => if lv <= rv then left else right
          | _, _ => left
      match data[i]?, data[smaller]? with
      | some vi, some vs =>
        if vi > vs then bmSiftDown (bmSwap data i smaller) size smaller f'
        else data
      | _, _ => data
-- !benchmark @end global_aux

-- ── Implementation stubs ──────────────────────────────────────

-- !benchmark @start code_aux def=insert
-- !benchmark @end code_aux def=insert

def BinomialHeap.insert (self : BinomialHeap) (val : Int) : BinomialHeap :=
-- !benchmark @start code def=insert
  let data := self.heap ++ [val]
  let i    := data.length - 1
  { heap := bmSiftUp data i i }
-- !benchmark @end code def=insert

-- !benchmark @start code_aux def=peek
-- !benchmark @end code_aux def=peek

-- @review human: panics on empty heap (Python AttributeError on min_node.val)
def BinomialHeap.peek (self : BinomialHeap) : Int :=
-- !benchmark @start code def=peek
  match self.heap[0]? with
  | some v => v
  | none   => panic! "peek: empty heap"
-- !benchmark @end code def=peek

-- !benchmark @start code_aux def=is_empty
-- !benchmark @end code_aux def=is_empty

def BinomialHeap.is_empty (self : BinomialHeap) : Bool :=
-- !benchmark @start code def=is_empty
  self.heap.isEmpty
-- !benchmark @end code def=is_empty

-- !benchmark @start code_aux def=delete_min
-- !benchmark @end code_aux def=delete_min

-- @review human: panics on empty heap
def BinomialHeap.delete_min (self : BinomialHeap) : Int × BinomialHeap :=
-- !benchmark @start code def=delete_min
  if self.heap.isEmpty then panic! "delete_min: empty heap"
  else
    let minVal := self.heap[0]!
    let n := self.heap.length
    if n == 1 then (minVal, { heap := [] })
    else
      let swapped := bmSwap self.heap 0 (n - 1)
      let newData := swapped.dropLast
      let newData := bmSiftDown newData (n - 1) 0 (n - 1)
      (minVal, { heap := newData })
-- !benchmark @end code def=delete_min
