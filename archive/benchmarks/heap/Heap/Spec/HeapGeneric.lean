import Heap.Harness

/-!
# Heap.Spec.HeapGeneric

Specifications for the generic integer heap with position-map (HeapGeneric.lean). Each `spec_*` is a property over an
arbitrary `impl : RepoImpl`.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- Look up an item's index in a position map (spec-local copy of the impl helper). -/
def spec_helper_genericheap_find_pos (pm : List (Int × Nat)) (item : Int) : Option Nat :=
  (pm.find? (fun p => p.1 == item)).map (·.2)

/-- The item stored in row `i` (`arr[i][0]`), if present. -/
def spec_helper_genericheap_row_item_at (h : GenericHeap) (i : Nat) : Option Int :=
  h.arr[i]?.bind (·[0]?)

/-- The key stored in row `i` (`arr[i][1]`), if present. -/
def spec_helper_genericheap_row_key_at (h : GenericHeap) (i : Nat) : Option Int :=
  h.arr[i]?.bind (·[1]?)

/-- Row `i` is a well-formed `[item, key]` pair whose item round-trips through `posMap`
back to index `i`. -/
def spec_helper_genericheap_active_row_wf (h : GenericHeap) (i : Nat) : Bool :=
  match h.arr[i]? with
  | some [item, _key] => spec_helper_genericheap_find_pos h.posMap item == some i
  | _ => false

/-- A `posMap` entry `(item, idx)` points at an active index whose row carries that item. -/
def spec_helper_genericheap_pos_entry_wf (h : GenericHeap) (p : Int × Nat) : Bool :=
  decide (p.2 < h.size) && (spec_helper_genericheap_row_item_at h p.2 == some p.1)

/-- Child `child` of `i` (if active) has key no greater than `i`'s key — the heap keeps
the LARGER key nearer the root (`heap_generic.py` is a max-heap by key). -/
def spec_helper_genericheap_child_le (h : GenericHeap) (i child : Nat) : Bool :=
  if child < h.size then
    match spec_helper_genericheap_row_key_at h i, spec_helper_genericheap_row_key_at h child with
    | some pk, some ck => decide (ck ≤ pk)
    | _, _ => false
  else true

/-- The active prefix satisfies the (max-by-key) heap-order property. -/
def spec_helper_genericheap_heap_ordered (h : GenericHeap) : Bool :=
  (List.range h.size).all (fun i =>
    spec_helper_genericheap_child_le h i (2 * i + 1) &&
    spec_helper_genericheap_child_le h i (2 * i + 2))

/-- Well-formedness (representation invariant) of a `GenericHeap`: active size within
bounds, unique `posMap` keys, every active row is a `[item, key]` pair round-tripping
through `posMap`, every `posMap` entry points at a matching active row, and the active
prefix is heap-ordered by key. API-built heaps maintain this invariant. -/
def spec_helper_genericheap_wf (h : GenericHeap) : Bool :=
  decide (h.size ≤ h.arr.length) &&
  decide ((h.posMap.map Prod.fst).Nodup) &&
  (List.range h.size).all (spec_helper_genericheap_active_row_wf h) &&
  h.posMap.all (spec_helper_genericheap_pos_entry_wf h) &&
  spec_helper_genericheap_heap_ordered h

/-- `get_top` of an empty `GenericHeap` (size = 0) returns `none`. -/
def spec_genericheap_get_top_empty (impl : RepoImpl) : Prop :=
  ∀ (h : GenericHeap),
    h.size = 0 →
    impl.heap.genericHeapGetTop h = none

/-- Calling `insert_item` on any `GenericHeap` increases `size` by exactly 1. -/
def spec_genericheap_insert_size_grows (impl : RepoImpl) : Prop :=
  ∀ (h : GenericHeap) (k v : Int),
    (impl.heap.genericHeapInsertItem h k v).size = h.size + 1

/-- After inserting a single item `(k, v)` into an empty heap, `get_top` returns `some [k, v]`. -/
def spec_genericheap_insert_singleton_get_top (impl : RepoImpl) : Prop :=
  ∀ (k v : Int),
    impl.heap.genericHeapGetTop
      (impl.heap.genericHeapInsertItem
        { arr := [], posMap := [], size := 0 } k v)
    = some [k, v]

/-- After inserting `(1, 10)` then `(2, 20)`, `get_top` returns `some [2, 20]` (max-by-key). -/
def spec_genericheap_insert_two_items_top_is_larger_key (impl : RepoImpl) : Prop :=
  impl.heap.genericHeapGetTop
    (impl.heap.genericHeapInsertItem
      (impl.heap.genericHeapInsertItem
        { arr := [], posMap := [], size := 0 } 1 10) 2 20)
  = some [2, 20]

/-- Deleting an absent item is a no-op: size is unchanged. -/
def spec_genericheap_delete_missing_no_op (impl : RepoImpl) : Prop :=
  ∀ (h : GenericHeap) (item : Int),
    item ∉ h.posMap.map Prod.fst →
    impl.heap.genericHeapDeleteItem h item = h

/-- Deleting the only item in a one-element heap leaves the heap with size 0. -/
def spec_genericheap_delete_only_item_zeroes_size (impl : RepoImpl) : Prop :=
  ∀ (item value : Int),
    (impl.heap.genericHeapDeleteItem
      (impl.heap.genericHeapInsertItem
        { arr := [], posMap := [], size := 0 } item value) item).size = 0

/-- After deleting the only item, `get_top` returns `none`. -/
def spec_genericheap_delete_only_item_get_top_none (impl : RepoImpl) : Prop :=
  ∀ (item value : Int),
    impl.heap.genericHeapGetTop
      (impl.heap.genericHeapDeleteItem
        (impl.heap.genericHeapInsertItem
          { arr := [], posMap := [], size := 0 } item value) item)
    = none

/-- `extract_top` of an empty heap returns `(none, empty)`. -/
def spec_genericheap_extract_top_empty (impl : RepoImpl) : Prop :=
  ∀ (h : GenericHeap),
    h.size = 0 →
    impl.heap.genericHeapExtractTop h = (none, h)

/-- `extract_top` of a one-element heap returns `(some [k, v], empty_heap)`. -/
def spec_genericheap_extract_top_singleton (impl : RepoImpl) : Prop :=
  ∀ (k v : Int),
    let (top, h') := impl.heap.genericHeapExtractTop
      (impl.heap.genericHeapInsertItem
        { arr := [], posMap := [], size := 0 } k v)
    top = some [k, v] ∧ h'.size = 0

/-- After inserting `(1, 10)` then `(2, 20)`, `extract_top` returns `some [2, 20]` and size 1. -/
def spec_genericheap_extract_top_two_items_returns_max_key (impl : RepoImpl) : Prop :=
  let (top, h') := impl.heap.genericHeapExtractTop
    (impl.heap.genericHeapInsertItem
      (impl.heap.genericHeapInsertItem
        { arr := [], posMap := [], size := 0 } 1 10) 2 20)
  top = some [2, 20] ∧ h'.size = 1

/-- Updating an absent item is a no-op: size is unchanged. -/
def spec_genericheap_update_missing_no_op (impl : RepoImpl) : Prop :=
  ∀ (h : GenericHeap) (item value : Int),
    item ∉ h.posMap.map Prod.fst →
    impl.heap.genericHeapUpdateItem h item value = h

/-- After inserting `(1, 10)` and updating item 1's key to 50, `get_top` returns `some [1, 50]`. -/
def spec_genericheap_update_changes_key_concrete (impl : RepoImpl) : Prop :=
  impl.heap.genericHeapGetTop
    (impl.heap.genericHeapUpdateItem
      (impl.heap.genericHeapInsertItem
        { arr := [], posMap := [], size := 0 } 1 10) 1 50)
  = some [1, 50]

/-- After inserting `(1, 10)`, `(2, 20)`, updating item 1's key to 999 promotes it to the top. -/
def spec_genericheap_update_promotes_item_to_top (impl : RepoImpl) : Prop :=
  impl.heap.genericHeapGetTop
    (impl.heap.genericHeapUpdateItem
      (impl.heap.genericHeapInsertItem
        (impl.heap.genericHeapInsertItem
          { arr := [], posMap := [], size := 0 } 1 10) 2 20) 1 999)
  = some [1, 999]

/-- `extract_top` returns the same optional row that `get_top` observes. Requires `h` to
be well-formed (every active row is a `[item, key]` pair), so `extract_top`'s inner
`arr[0][0]` lookup succeeds exactly when `get_top` reports a row. -/
def spec_genericheap_extract_top_returns_get_top (impl : RepoImpl) : Prop :=
  ∀ (h : GenericHeap),
    spec_helper_genericheap_wf h = true →
    (impl.heap.genericHeapExtractTop h).1 = impl.heap.genericHeapGetTop h

/-- Universal: whenever `get_top` reports no row, `extract_top` also returns no row. -/
def spec_genericheap_extract_top_when_get_top_empty (impl : RepoImpl) : Prop :=
  ∀ (h : GenericHeap),
    impl.heap.genericHeapGetTop h = none →
    (impl.heap.genericHeapExtractTop h).1 = none

/-- If item `i` is currently the top with old value `ov`, and we update it to a strictly
larger value `new_value > ov`, then `i` remains the top with the updated value. Requires
`h` to be well-formed (`posMap` in sync with `arr` and heap-ordered by key) so the update
is applied and the strictly-increased key keeps `i` at the root. The increase is strict
because the impl's sift bubbles a child up on *equal* keys. -/
def spec_genericheap_update_top_item (impl : RepoImpl) : Prop :=
  ∀ (h : GenericHeap) (item old_value new_value : Int),
    spec_helper_genericheap_wf h = true →
    impl.heap.genericHeapGetTop h = some [item, old_value] →
    old_value < new_value →
    impl.heap.genericHeapGetTop
      (impl.heap.genericHeapUpdateItem h item new_value)
      = some [item, new_value]

/-- Deleting the current top item changes the next extracted row: the new extracted row
is no longer `[item, value]`. Requires `h` to be well-formed (`posMap` in sync with `arr`,
unique keys) so `delete_item` actually finds and removes the top rather than no-opping. -/
def spec_genericheap_delete_item_removes_current_top (impl : RepoImpl) : Prop :=
  ∀ (h : GenericHeap) (item value : Int),
    spec_helper_genericheap_wf h = true →
    impl.heap.genericHeapGetTop h = some [item, value] →
    (impl.heap.genericHeapExtractTop
      (impl.heap.genericHeapDeleteItem h item)).1 ≠ some [item, value]
