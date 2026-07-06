-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Heap.Impl.RandomizedHeap

Polymorphic randomized min-heap. Translated from
`data_structures/heap/randomized_heap.py` in TheAlgorithms/Python.

The Python `RandomizedHeapNode.merge` calls `random.choice([True, False])` to
randomly swap left and right children before recursing. This cannot be modelled
in a pure, deterministic Lean function. The Lean translation uses a deterministic
merge (always recurse into the left subtree without swapping) — the resulting
structure is a valid leftist-style min-heap with the same observable API
behaviour.

`top` returns `Option α` rather than raising `IndexError` on an empty heap.

@review human: random.choice omitted — deterministic merge used instead.

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
Implement only the function bodies.
-/

-- ── Core data types (DO NOT MODIFY) ──────────────────────────

/-- Node in a randomized heap tree. -/
inductive RandomizedHeapNode (α : Type) where
  | mk (value : α) (left right : Option (RandomizedHeapNode α)) : RandomizedHeapNode α
  deriving Repr, BEq

/-- Polymorphic randomized min-heap. `_root` is `none` iff the heap is empty. -/
structure RandomizedHeap (α : Type) where
  _root : Option (RandomizedHeapNode α)
  deriving Repr, BEq

namespace RandomizedHeap

variable {α : Type}

-- ── API signatures (DO NOT MODIFY) ───────────────────────────
abbrev InsertSig       [Ord α] := RandomizedHeap α → α → RandomizedHeap α
-- @review human: Python raises IndexError on empty; Lean returns none.
abbrev TopSig          [Ord α] := RandomizedHeap α → Option α
abbrev ToSortedListSig [Ord α] := RandomizedHeap α → List α
abbrev ClearSig                := RandomizedHeap α → RandomizedHeap α

end RandomizedHeap

-- !benchmark @start global_aux
-- Deterministic merge (replaces the random.choice variant in Python).
-- Both merge implementations satisfy the min-heap invariant.
private def rhMerge {α : Type} [Ord α]
    (a b : Option (RandomizedHeapNode α)) (fuel : Nat) : Option (RandomizedHeapNode α) :=
  match fuel with
  | 0      => a
  | f' + 1 =>
    match a, b with
    | none, x | x, none => x
    | some (.mk av al ar), some (.mk bv bl br) =>
      if Ord.compare av bv != .gt then
        -- av ≤ bv: av wins; merge av's left with b (deterministic, no swap)
        let merged := rhMerge al b f'
        some (.mk av merged ar)
      else
        -- bv < av: bv wins; merge a with bv's left (deterministic, no swap)
        let merged := rhMerge a bl f'
        some (.mk bv merged br)
-- !benchmark @end global_aux

-- ── Implementation stubs ──────────────────────────────────────

-- !benchmark @start code_aux def=insert
-- !benchmark @end code_aux def=insert

def RandomizedHeap.insert {α : Type} [Ord α]
    (self : RandomizedHeap α) (value : α) : RandomizedHeap α :=
-- !benchmark @start code def=insert
  let node := some (.mk value none none)
  { _root := rhMerge self._root node 1024 }
-- !benchmark @end code def=insert

-- !benchmark @start code_aux def=top
-- !benchmark @end code_aux def=top

-- @review human: Python raises IndexError on empty; Lean returns none.
def RandomizedHeap.top {α : Type} [Ord α] (self : RandomizedHeap α) : Option α :=
-- !benchmark @start code def=top
  self._root.map (fun n => match n with | .mk v _ _ => v)
-- !benchmark @end code def=top

-- !benchmark @start code_aux def=to_sorted_list
-- !benchmark @end code_aux def=to_sorted_list

-- Pops elements one by one into ascending order (min-heap invariant).
def RandomizedHeap.to_sorted_list {α : Type} [Ord α]
    (self : RandomizedHeap α) : List α :=
-- !benchmark @start code def=to_sorted_list
  let rec go (root : Option (RandomizedHeapNode α)) (fuel : Nat) : List α :=
    match fuel with
    | 0 => []
    | f' + 1 =>
      match root with
      | none              => []
      | some (.mk v l r) =>
        let newRoot := rhMerge l r f'
        v :: go newRoot f'
  go self._root 1024
-- !benchmark @end code def=to_sorted_list

-- !benchmark @start code_aux def=clear
-- !benchmark @end code_aux def=clear

def RandomizedHeap.clear {α : Type} (_self : RandomizedHeap α) : RandomizedHeap α :=
-- !benchmark @start code def=clear
  { _root := none }
-- !benchmark @end code def=clear
