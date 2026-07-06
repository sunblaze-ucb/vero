-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Heap.Impl.SkewHeap

Polymorphic skew min-heap. Translated from
`data_structures/heap/skew_heap.py` in TheAlgorithms/Python.

A skew heap is a self-adjusting heap implemented as a binary tree. The merge
operation (the core primitive) swaps left and right children on every step,
giving amortised O(log n) complexity. The Python `SkewNode.merge` is a
static method translating directly to a private recursive function here.

`top` and `pop` return `Option` rather than panicking on an empty heap
(Python raises `IndexError`).

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
Implement only the function bodies.
-/

-- ── Core data types (DO NOT MODIFY) ──────────────────────────

/-- Node in a skew heap tree. -/
inductive SkewNode (α : Type) where
  | mk (value : α) (left right : Option (SkewNode α)) : SkewNode α
  deriving Repr, BEq

/-- Polymorphic skew min-heap. `_root` is `none` iff the heap is empty. -/
structure SkewHeap (α : Type) where
  _root : Option (SkewNode α)
  deriving Repr, BEq

namespace SkewHeap

variable {α : Type}

-- ── API signatures (DO NOT MODIFY) ───────────────────────────
abbrev InsertSig [Ord α] := SkewHeap α → α → SkewHeap α
-- @review human: Python raises IndexError on empty; Lean returns none.
abbrev TopSig    [Ord α] := SkewHeap α → Option α
abbrev PopSig    [Ord α] := SkewHeap α → Option α × SkewHeap α
abbrev ClearSig          := SkewHeap α → SkewHeap α

end SkewHeap

-- !benchmark @start global_aux
-- Merge two skew heap roots (min-heap: smaller root wins).
-- Swaps left/right on every descent (the skew heap self-adjustment step).
-- fuel bounds recursion depth.
private def skewMerge {α : Type} [Ord α]
    (a b : Option (SkewNode α)) (fuel : Nat) : Option (SkewNode α) :=
  match fuel with
  | 0      => a
  | f' + 1 =>
    match a, b with
    | none, x | x, none => x
    | some (.mk av al ar), some (.mk bv bl br) =>
      if Ord.compare av bv != .gt then
        -- av ≤ bv: av wins; merge av's right with b, swap left↔right
        let merged := skewMerge ar b f'
        some (.mk av merged al)
      else
        -- bv < av: bv wins; merge a with bv's right, swap left↔right
        let merged := skewMerge a br f'
        some (.mk bv merged bl)
-- !benchmark @end global_aux

-- ── Implementation stubs ──────────────────────────────────────

-- !benchmark @start code_aux def=insert
-- !benchmark @end code_aux def=insert

def SkewHeap.insert {α : Type} [Ord α] (self : SkewHeap α) (value : α) : SkewHeap α :=
-- !benchmark @start code def=insert
  let node := some (.mk value none none)
  { _root := skewMerge self._root node 1024 }
-- !benchmark @end code def=insert

-- !benchmark @start code_aux def=top
-- !benchmark @end code_aux def=top

-- @review human: Python raises IndexError on empty heap; Lean returns none.
def SkewHeap.top {α : Type} [Ord α] (self : SkewHeap α) : Option α :=
-- !benchmark @start code def=top
  self._root.map (fun n => match n with | .mk v _ _ => v)
-- !benchmark @end code def=top

-- !benchmark @start code_aux def=pop
-- !benchmark @end code_aux def=pop

-- @review human: Python raises IndexError on empty heap; Lean returns (none, self).
def SkewHeap.pop {α : Type} [Ord α] (self : SkewHeap α) : Option α × SkewHeap α :=
-- !benchmark @start code def=pop
  match self._root with
  | none             => (none, self)
  | some (.mk v l r) =>
    let newRoot := skewMerge l r 1024
    (some v, { _root := newRoot })
-- !benchmark @end code def=pop

-- !benchmark @start code_aux def=clear
-- !benchmark @end code_aux def=clear

def SkewHeap.clear {α : Type} (self : SkewHeap α) : SkewHeap α :=
-- !benchmark @start code def=clear
  { _root := none }
-- !benchmark @end code def=clear
