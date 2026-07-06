-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Heap.Impl.MaxHeap

Integer max-heap (1-indexed internally, sentinel-free in the Lean model).
Translated from `data_structures/heap/max_heap.py` in TheAlgorithms/Python.

The Python `BinaryHeap` stores elements in a 1-indexed list with a dummy `0`
at position 0. The Lean translation uses a 0-indexed `List Int` (`data`) for
simplicity; the heap operations are re-indexed accordingly.

`pop` returns `Option (Int × BinaryHeap)` instead of panicking on an empty
heap (Python raises `IndexError`).

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
Implement only the function bodies.
-/

-- ── Core data type (DO NOT MODIFY) ───────────────────────────

/-- Integer max-heap backed by a 0-indexed list. -/
structure BinaryHeap where
  data : List Int
  deriving Repr, BEq, Inhabited

namespace BinaryHeap

-- ── API signatures (DO NOT MODIFY) ───────────────────────────
abbrev InsertSig  := BinaryHeap → Int → BinaryHeap
abbrev PopSig     := BinaryHeap → Int × BinaryHeap
abbrev GetListSig := BinaryHeap → List Int
abbrev SizeSig    := BinaryHeap → Nat

end BinaryHeap

-- !benchmark @start global_aux
-- Swap elements at positions i and j in a list of Int.
private def bhSwap (l : List Int) (i j : Nat) : List Int :=
  match l[i]?, l[j]? with
  | some vi, some vj =>
    l.mapIdx fun k x => if k == i then vj else if k == j then vi else x
  | _, _ => l

-- Sift element at position i upward toward the root (max-heap).
-- fuel ≤ i: the tree depth is at most i steps.
private def bhSwapUp (data : List Int) (i : Nat) (fuel : Nat) : List Int :=
  match fuel with
  | 0      => data
  | f' + 1 =>
    if i == 0 then data
    else
      let p := (i - 1) / 2
      match data[i]?, data[p]? with
      | some vi, some vp =>
        if vi > vp then bhSwapUp (bhSwap data i p) p f'
        else data
      | _, _ => data

-- Sift element at position i downward (max-heap).
-- fuel = current heap size — bounds the descent.
private def bhSwapDown (data : List Int) (size : Nat) (i : Nat) (fuel : Nat) : List Int :=
  match fuel with
  | 0      => data
  | f' + 1 =>
    let left  := 2 * i + 1
    let right := 2 * i + 2
    if left >= size then data   -- leaf node, done
    else
      -- Choose the larger child.
      let bigger :=
        if right >= size then left
        else match data[left]?, data[right]? with
          | some lv, some rv => if lv >= rv then left else right
          | _, _ => left
      match data[i]?, data[bigger]? with
      | some vi, some vc =>
        if vi < vc then bhSwapDown (bhSwap data i bigger) size bigger f'
        else data
      | _, _ => data
-- !benchmark @end global_aux

-- ── Implementation stubs ──────────────────────────────────────

-- !benchmark @start code_aux def=insert
-- !benchmark @end code_aux def=insert

def BinaryHeap.insert (self : BinaryHeap) (value : Int) : BinaryHeap :=
-- !benchmark @start code def=insert
  let data := self.data ++ [value]
  let i    := data.length - 1
  { data := bhSwapUp data i i }
-- !benchmark @end code def=insert

-- !benchmark @start code_aux def=pop
-- !benchmark @end code_aux def=pop

-- @review human: panics on empty heap (Python raises IndexError); Inhabited Int allows panic!
def BinaryHeap.pop (self : BinaryHeap) : Int × BinaryHeap :=
-- !benchmark @start code def=pop
  if self.data.isEmpty then panic! "pop: empty heap"
  else
    let maxVal := self.data[0]!
    let n := self.data.length
    if n == 1 then (maxVal, { data := [] })
    else
      -- Move last element to root, drop last slot, then sift down.
      let swapped := bhSwap self.data 0 (n - 1)
      let newData := swapped.dropLast
      let newData := bhSwapDown newData (n - 1) 0 (n - 1)
      (maxVal, { data := newData })
-- !benchmark @end code def=pop

-- !benchmark @start code_aux def=get_list
-- !benchmark @end code_aux def=get_list

def BinaryHeap.get_list (self : BinaryHeap) : List Int :=
-- !benchmark @start code def=get_list
  self.data
-- !benchmark @end code def=get_list

-- !benchmark @start code_aux def=size
-- !benchmark @end code_aux def=size

def BinaryHeap.size (self : BinaryHeap) : Nat :=
-- !benchmark @start code def=size
  self.data.length
-- !benchmark @end code def=size
