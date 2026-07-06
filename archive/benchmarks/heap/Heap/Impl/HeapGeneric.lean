-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Heap.Impl.HeapGeneric

Generic min-heap with position-map for O(log n) decrease-key.
Translated from `data_structures/heap/heap_generic.py` in TheAlgorithms/Python.

The Python `Heap` class is renamed to `GenericHeap` to avoid a name collision
with `Heap α` in `Heap.Impl.Heap`.  The `key` parameter (a callable) is fixed
to the identity function here (`key(x) = x`); all item and key values are
`Int`.

Each element of `arr` is stored as `[item, key_val] : List Int`.
`posMap` maps `item → index_in_arr` for O(log n) `update_item` /
`delete_item`.

@review human: heap_generic.py's heapify_up/down logic keeps the element with the
LARGER key at position 0 (condition "not _cmp(child, parent)" = child >= parent
triggers swap, moving larger values upward). This is effectively a max-heap by key.

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
Implement only the function bodies.
-/

-- ── Core data type (DO NOT MODIFY) ───────────────────────────

/-- Generic integer min-heap with position tracking.
`arr` holds `[item, key_val]` pairs; only the first `size` are active.
`posMap` maps each active item to its current index in `arr`. -/
structure GenericHeap where
  arr    : List (List Int)    -- element i is [item, key_val]
  posMap : List (Int × Nat)   -- item → index in arr
  size   : Nat
  deriving Repr

namespace GenericHeap

-- ── API signatures (DO NOT MODIFY) ───────────────────────────
abbrev InsertItemSig  := GenericHeap → Int → Int → GenericHeap
-- get_top returns the top element ([item, key_val]) or none if empty.
abbrev GetTopSig      := GenericHeap → Option (List Int)
-- extract_top returns the top element and the updated heap.
abbrev ExtractTopSig  := GenericHeap → Option (List Int) × GenericHeap
abbrev UpdateItemSig  := GenericHeap → Int → Int → GenericHeap
abbrev DeleteItemSig  := GenericHeap → Int → GenericHeap

end GenericHeap

-- !benchmark @start global_aux
-- Look up item's index in posMap. Returns none if item not present.
private def ghFindPos (pm : List (Int × Nat)) (item : Int) : Option Nat :=
  (pm.find? (fun p => p.1 == item)).map (·.2)

-- Update item's index in posMap.
private def ghSetPos (pm : List (Int × Nat)) (item : Int) (idx : Nat) : List (Int × Nat) :=
  if pm.any (fun p => p.1 == item) then
    pm.map fun p => if p.1 == item then (item, idx) else p
  else (item, idx) :: pm

-- Remove item from posMap.
private def ghDelPos (pm : List (Int × Nat)) (item : Int) : List (Int × Nat) :=
  pm.filter (fun p => p.1 != item)

-- Compare arr[i][1] < arr[j][1] (ordering by key_val).
private def ghCmp (arr : List (List Int)) (i j : Nat) : Bool :=
  match arr[i]?.bind (·[1]?), arr[j]?.bind (·[1]?) with
  | some ki, some kj => ki < kj
  | _, _ => false

-- Swap arr[i] and arr[j]; update posMap for both elements.
private def ghSwap (arr : List (List Int)) (pm : List (Int × Nat)) (i j : Nat)
    : List (List Int) × List (Int × Nat) :=
  match arr[i]?, arr[j]? with
  | some ei, some ej =>
    let arr' := arr.mapIdx fun k x => if k == i then ej else if k == j then ei else x
    let pm' := match ei[0]?, ej[0]? with
      | some ik, some jk => ghSetPos (ghSetPos pm ik j) jk i
      | _, _ => pm
    (arr', pm')
  | _, _ => (arr, pm)

-- Find the "valid parent": the index (among i, left(i), right(i)) whose key_val
-- is NOT less than the others (Python: not _cmp(child, vp) picks child when
-- child_key >= vp_key, bubbling larger keys up → this is effectively a max-heap).
private def ghValidParent (arr : List (List Int)) (size : Nat) (i : Nat) : Nat :=
  let left  := 2 * i + 1
  let right := 2 * i + 2
  let vp := i
  let vp := if left < size && ¬ghCmp arr left vp then left else vp
  let vp := if right < size && ¬ghCmp arr right vp then right else vp
  vp

-- Sift element at index upward (swap while child_key >= parent_key).
private def ghSiftUp (arr : List (List Int)) (pm : List (Int × Nat)) (idx : Nat) (fuel : Nat)
    : List (List Int) × List (Int × Nat) :=
  match fuel with
  | 0 => (arr, pm)
  | f' + 1 =>
    if idx == 0 then (arr, pm)
    else
      let p := (idx - 1) / 2
      if ¬ghCmp arr idx p then   -- arr[idx][1] >= arr[p][1] → swap
        let (arr', pm') := ghSwap arr pm idx p
        ghSiftUp arr' pm' p f'
      else (arr, pm)

-- Sift element at index downward.
private def ghSiftDown (arr : List (List Int)) (pm : List (Int × Nat)) (size : Nat)
    (idx : Nat) (fuel : Nat) : List (List Int) × List (Int × Nat) :=
  match fuel with
  | 0 => (arr, pm)
  | f' + 1 =>
    let vp := ghValidParent arr size idx
    if vp != idx then
      let (arr', pm') := ghSwap arr pm idx vp
      ghSiftDown arr' pm' size vp f'
    else (arr, pm)
-- !benchmark @end global_aux

-- ── Implementation stubs ──────────────────────────────────────

-- !benchmark @start code_aux def=insert_item
-- !benchmark @end code_aux def=insert_item

def GenericHeap.insert_item (self : GenericHeap) (item : Int) (item_value : Int) : GenericHeap :=
-- !benchmark @start code def=insert_item
  let entry := [item, item_value]
  let arr   := if self.arr.length == self.size then self.arr ++ [entry]
               else self.arr.mapIdx fun k x => if k == self.size then entry else x
  let pm    := ghSetPos self.posMap item self.size
  let size' := self.size + 1
  let (arr', pm') := ghSiftUp arr pm (size' - 1) (size' - 1)
  { arr := arr', posMap := pm', size := size' }
-- !benchmark @end code def=insert_item

-- !benchmark @start code_aux def=get_top
-- !benchmark @end code_aux def=get_top

def GenericHeap.get_top (self : GenericHeap) : Option (List Int) :=
-- !benchmark @start code def=get_top
  if self.size == 0 then none else self.arr[0]?
-- !benchmark @end code def=get_top

-- delete_item is defined before extract_top because extract_top calls it.

-- !benchmark @start code_aux def=delete_item
-- !benchmark @end code_aux def=delete_item

def GenericHeap.delete_item (self : GenericHeap) (item : Int) : GenericHeap :=
-- !benchmark @start code def=delete_item
  match ghFindPos self.posMap item with
  | none => self   -- item not present; no-op
  | some idx =>
    let pm'   := ghDelPos self.posMap item
    let size' := if self.size == 0 then 0 else self.size - 1
    let lastIdx := size'  -- last active index after shrink
    if idx == lastIdx then
      -- Item is already the last element; just shrink.
      { arr := self.arr, posMap := pm', size := size' }
    else
      -- Replace arr[idx] with arr[lastIdx]; update posMap; re-heapify.
      match self.arr[lastIdx]?.bind (·[0]?) with
      | none => { arr := self.arr, posMap := pm', size := size' }
      | some lastItem =>
        let replacement := self.arr[lastIdx]?.getD []
        let arr' := self.arr.mapIdx fun k x => if k == idx then replacement else x
        let pm'' := ghSetPos pm' lastItem idx
        let (arr'', pm''') := ghSiftUp arr' pm'' idx idx
        let (arr''', pm'''') := ghSiftDown arr'' pm''' size' idx size'
        { arr := arr''', posMap := pm'''', size := size' }
-- !benchmark @end code def=delete_item

-- !benchmark @start code_aux def=extract_top
-- !benchmark @end code_aux def=extract_top

def GenericHeap.extract_top (self : GenericHeap) : Option (List Int) × GenericHeap :=
-- !benchmark @start code def=extract_top
  match self.get_top, self.arr[0]?.bind (·[0]?) with
  | some topEntry, some topItem =>
    let heap' := self.delete_item topItem
    (some topEntry, heap')
  | _, _ => (none, self)
-- !benchmark @end code def=extract_top

-- !benchmark @start code_aux def=update_item
-- !benchmark @end code_aux def=update_item

def GenericHeap.update_item (self : GenericHeap) (item : Int) (item_value : Int) : GenericHeap :=
-- !benchmark @start code def=update_item
  match ghFindPos self.posMap item with
  | none => self   -- item not present; no-op
  | some idx =>
    let arr' := self.arr.mapIdx fun k x => if k == idx then [item, item_value] else x
    let (arr'', pm') := ghSiftUp arr' self.posMap idx idx
    let (arr''', pm'') := ghSiftDown arr'' pm' self.size idx self.size
    { arr := arr''', posMap := pm'', size := self.size }
-- !benchmark @end code def=update_item
