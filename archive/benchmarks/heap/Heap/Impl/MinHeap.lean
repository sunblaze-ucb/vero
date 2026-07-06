-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Heap.Impl.MinHeap

Named-node min-heap with decrease-key support. Translated from
`data_structures/heap/min_heap.py` in TheAlgorithms/Python.

The Python `Node` has a `name : str` and `val : int`; nodes are compared by
`val`. `MinHeap` stores a heap array, a name→index mapping (`idx_of_element`),
and a name→value mapping (`heap_dict`).

Only four APIs are exposed in this benchmark:
`get_parent_idx`, `get_left_child_idx`, `get_right_child_idx`, `is_empty`.
All take `Int` indices matching the Python convention (parent of root = −1).

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
Implement only the function bodies.
-/

-- ── Core data types (DO NOT MODIFY) ──────────────────────────

/-- A named node in the min-heap. Compared by `val`. -/
structure MinNode where
  name : String
  val  : Int
  deriving Repr, BEq

/-- Min-heap over `MinNode` values.
`heap` is the 0-indexed heap array.
`idxOf` maps node name → its current index in `heap`.
`heapDict` maps node name → current value (for O(1) get_value). -/
structure MinHeap where
  heap     : List MinNode
  idxOf    : List (String × Nat)
  heapDict : List (String × Int)
  deriving Repr

namespace MinHeap

-- ── API signatures (DO NOT MODIFY) ───────────────────────────
abbrev GetParentIdxSig    := MinHeap → Int → Int
abbrev GetLeftChildIdxSig := MinHeap → Int → Int
abbrev GetRightChildIdxSig:= MinHeap → Int → Int
abbrev IsEmptySig         := MinHeap → Bool

end MinHeap

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- ── Implementation stubs ──────────────────────────────────────

-- !benchmark @start code_aux def=get_parent_idx
-- !benchmark @end code_aux def=get_parent_idx

-- @review human: Python uses floor division (idx-1)//2; Lean Int / matches (same semantics).
-- Parent of the root (idx=0) returns -1 (sentinel meaning "no parent").
def MinHeap.get_parent_idx (_self : MinHeap) (idx : Int) : Int :=
-- !benchmark @start code def=get_parent_idx
  (idx - 1) / 2
-- !benchmark @end code def=get_parent_idx

-- !benchmark @start code_aux def=get_left_child_idx
-- !benchmark @end code_aux def=get_left_child_idx

def MinHeap.get_left_child_idx (_self : MinHeap) (idx : Int) : Int :=
-- !benchmark @start code def=get_left_child_idx
  idx * 2 + 1
-- !benchmark @end code def=get_left_child_idx

-- !benchmark @start code_aux def=get_right_child_idx
-- !benchmark @end code_aux def=get_right_child_idx

def MinHeap.get_right_child_idx (_self : MinHeap) (idx : Int) : Int :=
-- !benchmark @start code def=get_right_child_idx
  idx * 2 + 2
-- !benchmark @end code def=get_right_child_idx

-- !benchmark @start code_aux def=is_empty
-- !benchmark @end code_aux def=is_empty

def MinHeap.is_empty (self : MinHeap) : Bool :=
-- !benchmark @start code def=is_empty
  self.heap.isEmpty
-- !benchmark @end code def=is_empty
