-- !benchmark @start imports
-- !benchmark @end imports

/-!
# SortedcontainersCore.Impl.SortedList

Pure-functional Lean 4 model of Python's `SortedList` and `SortedKeyList`
from the `sortedcontainers` library.  Both types are modelled as sorted
`List α` (values in ascending `Ord` order, duplicates allowed for
`SortedList`).

`SortedKeyList` stores values sorted by the natural `Ord` order of `α`;
the Python key-function is not stored (see `@review` notes on
`bisect_key_left` / `bisect_key_right`).

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
Implement only the function bodies.
-/

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- ── Types (no markers — fixed vocabulary) ──────────────────────────────

/-- A sorted list.  Values are maintained in ascending order; duplicates
    are allowed.  Modelled as `List α` in Lean. -/
abbrev SortedContainers.SortedList (α : Type) := List α

/-- A sorted list with an external key function.  In this Lean model the
    key function is not stored; values are sorted by the natural `Ord`
    order of `α`. -/
abbrev SortedContainers.SortedKeyList (α : Type) := List α

-- ── Variable declaration ────────────────────────────────────────────────
-- @review human: original Python is universe-polymorphic (Type u); using
-- Type 0 here for compatibility with the monomorphic Bundle structure.
variable {α : Type} [Ord α] [BEq α] [Inhabited α]

-- ── Sig abbrevs (no markers — fixed vocabulary) ─────────────────────────

namespace SortedContainers

abbrev SortedListMkSig          := List α → SortedList α
abbrev SortedListContainsSig    := SortedList α → α → Bool
abbrev SortedListLenSig         := SortedList α → Nat
abbrev SortedListGetitemSig     := SortedList α → Nat → α
abbrev SortedListDelitemSig     := SortedList α → Nat → SortedList α
abbrev SortedListAddSig         := SortedList α → α → SortedList α
abbrev SortedListDiscardSig     := SortedList α → α → SortedList α
abbrev SortedListRemoveSig      := SortedList α → α → SortedList α
abbrev SortedListUpdateSig      := SortedList α → List α → SortedList α
abbrev SortedListExtendSig      := SortedList α → List α → SortedList α
abbrev SortedListBisectLeftSig  := SortedList α → α → Nat
abbrev SortedListBisectRightSig := SortedList α → α → Nat
abbrev SortedListCountSig       := SortedList α → α → Nat
abbrev SortedListIndexSig       := SortedList α → α → Nat → Nat → Nat
abbrev SortedListClearSig       := SortedList α → SortedList α
abbrev SortedListCopySig        := SortedList α → SortedList α
abbrev SortedListPopSig         := SortedList α → Nat → α
abbrev SortedListIrangeSig      := SortedList α → α → α → Bool → Bool → List α
abbrev SortedListIsliceSig      := SortedList α → Nat → Nat → Bool → List α
abbrev SortedListIterSig        := SortedList α → List α
abbrev SortedListReversedSig    := SortedList α → List α

abbrev SortedKeyListMkSig           := List α → SortedKeyList α
abbrev SortedKeyListContainsSig     := SortedKeyList α → α → Bool
abbrev SortedKeyListAddSig          := SortedKeyList α → α → SortedList α
abbrev SortedKeyListDiscardSig      := SortedKeyList α → α → SortedList α
abbrev SortedKeyListRemoveSig       := SortedKeyList α → α → SortedList α
abbrev SortedKeyListBisectLeftSig   := SortedKeyList α → α → Nat
abbrev SortedKeyListBisectRightSig  := SortedKeyList α → α → Nat
abbrev SortedKeyListCountSig        := SortedKeyList α → α → Nat
abbrev SortedKeyListIndexSig        := SortedKeyList α → α → Nat → Nat → Nat
abbrev SortedKeyListIrangeSig       := SortedKeyList α → α → α → Bool → Bool → List α
abbrev SortedKeyListClearSig        := SortedKeyList α → SortedList α
abbrev SortedKeyListCopySig         := SortedKeyList α → SortedList α
abbrev SortedKeyListUpdateSig       := SortedKeyList α → List α → SortedList α

end SortedContainers

-- ── Private sort helper ─────────────────────────────────────────────────

/-- Sort a list using the `Ord` instance (via Array.qsort). -/
def ordSort (lst : List α) : List α :=
  (lst.toArray.qsort (fun a b => Ord.compare a b == Ordering.lt)).toList

-- ── Binary-search helpers (exported for use by SortedSet/SortedDict) ───

-- @review human: termination via binary search convergence (hi − lo
-- strictly decreases every recursive call when lo < hi).
def bisectLeftGo (lst : List α) (val : α) (lo hi : Nat) : Nat :=
  if lo >= hi then lo
  else
    let mid := (lo + hi) / 2
    match lst[mid]? with
    | none   => lo
    | some x =>
      if Ord.compare x val == Ordering.lt
      then bisectLeftGo lst val (mid + 1) hi
      else bisectLeftGo lst val lo mid
termination_by hi - lo
decreasing_by
  all_goals simp_wf
  all_goals omega

-- @review human: same termination argument as bisectLeftGo.
def bisectRightGo (lst : List α) (val : α) (lo hi : Nat) : Nat :=
  if lo >= hi then lo
  else
    let mid := (lo + hi) / 2
    match lst[mid]? with
    | none   => lo
    | some x =>
      if Ord.compare x val == Ordering.gt
      then bisectRightGo lst val lo mid
      else bisectRightGo lst val (mid + 1) hi
termination_by hi - lo
decreasing_by
  all_goals simp_wf
  all_goals omega

/-- Insert `val` into a sorted list at its rightmost valid position. -/
def sortedInsert (lst : List α) (val : α) : List α :=
  let pos := bisectRightGo lst val 0 lst.length
  lst.take pos ++ [val] ++ lst.drop pos

-- ── SortedList implementations (LLM task) ──────────────────────────────

-- !benchmark @start code_aux def=sortedListMk
-- !benchmark @end code_aux def=sortedListMk

def SortedContainers.SortedList.mk (xs : List α) : SortedContainers.SortedList α :=
-- !benchmark @start code def=sortedListMk
  ordSort xs
-- !benchmark @end code def=sortedListMk

-- !benchmark @start code_aux def=sortedListContains
-- !benchmark @end code_aux def=sortedListContains

def SortedContainers.SortedList.contains (s0 : SortedContainers.SortedList α) (value : α) : Bool :=
-- !benchmark @start code def=sortedListContains
  let pos := bisectLeftGo s0 value 0 s0.length
  match s0[pos]? with
  | some x => x == value
  | none   => false
-- !benchmark @end code def=sortedListContains

-- !benchmark @start code_aux def=sortedListLen
-- !benchmark @end code_aux def=sortedListLen

def SortedContainers.SortedList.len (s0 : SortedContainers.SortedList α) : Nat :=
-- !benchmark @start code def=sortedListLen
  s0.length
-- !benchmark @end code def=sortedListLen

-- !benchmark @start code_aux def=sortedListGetitem
-- !benchmark @end code_aux def=sortedListGetitem

def SortedContainers.SortedList.getitem (s0 : SortedContainers.SortedList α) (index : Nat) : α :=
-- !benchmark @start code def=sortedListGetitem
  match s0[index]? with
  | some x => x
  | none   => default
-- !benchmark @end code def=sortedListGetitem

-- !benchmark @start code_aux def=sortedListDelitem
-- !benchmark @end code_aux def=sortedListDelitem

def SortedContainers.SortedList.delitem (s0 : SortedContainers.SortedList α) (index : Nat) : SortedContainers.SortedList α :=
-- !benchmark @start code def=sortedListDelitem
  s0.eraseIdx index
-- !benchmark @end code def=sortedListDelitem

-- !benchmark @start code_aux def=sortedListAdd
-- !benchmark @end code_aux def=sortedListAdd

def SortedContainers.SortedList.add (s0 : SortedContainers.SortedList α) (value : α) : SortedContainers.SortedList α :=
-- !benchmark @start code def=sortedListAdd
  sortedInsert s0 value
-- !benchmark @end code def=sortedListAdd

-- !benchmark @start code_aux def=sortedListDiscard
-- !benchmark @end code_aux def=sortedListDiscard

def SortedContainers.SortedList.discard (s0 : SortedContainers.SortedList α) (value : α) : SortedContainers.SortedList α :=
-- !benchmark @start code def=sortedListDiscard
  let pos := bisectLeftGo s0 value 0 s0.length
  match s0[pos]? with
  | some x => if x == value then s0.eraseIdx pos else s0
  | none   => s0
-- !benchmark @end code def=sortedListDiscard

-- !benchmark @start code_aux def=sortedListRemove
-- !benchmark @end code_aux def=sortedListRemove

-- Note: Python raises ValueError if not found; Lean returns s0 unchanged.
def SortedContainers.SortedList.remove (s0 : SortedContainers.SortedList α) (value : α) : SortedContainers.SortedList α :=
-- !benchmark @start code def=sortedListRemove
  SortedContainers.SortedList.discard s0 value
-- !benchmark @end code def=sortedListRemove

-- !benchmark @start code_aux def=sortedListUpdate
-- !benchmark @end code_aux def=sortedListUpdate

def SortedContainers.SortedList.update (s0 : SortedContainers.SortedList α) (iterable : List α) : SortedContainers.SortedList α :=
-- !benchmark @start code def=sortedListUpdate
  ordSort (s0 ++ iterable)
-- !benchmark @end code def=sortedListUpdate

-- !benchmark @start code_aux def=sortedListExtend
-- !benchmark @end code_aux def=sortedListExtend

def SortedContainers.SortedList.extend (s0 : SortedContainers.SortedList α) (values : List α) : SortedContainers.SortedList α :=
-- !benchmark @start code def=sortedListExtend
  SortedContainers.SortedList.update s0 values
-- !benchmark @end code def=sortedListExtend

-- !benchmark @start code_aux def=sortedListBisectLeft
-- !benchmark @end code_aux def=sortedListBisectLeft

def SortedContainers.SortedList.bisect_left (s0 : SortedContainers.SortedList α) (value : α) : Nat :=
-- !benchmark @start code def=sortedListBisectLeft
  bisectLeftGo s0 value 0 s0.length
-- !benchmark @end code def=sortedListBisectLeft

-- !benchmark @start code_aux def=sortedListBisectRight
-- !benchmark @end code_aux def=sortedListBisectRight

def SortedContainers.SortedList.bisect_right (s0 : SortedContainers.SortedList α) (value : α) : Nat :=
-- !benchmark @start code def=sortedListBisectRight
  bisectRightGo s0 value 0 s0.length
-- !benchmark @end code def=sortedListBisectRight

-- !benchmark @start code_aux def=sortedListCount
-- !benchmark @end code_aux def=sortedListCount

def SortedContainers.SortedList.count (s0 : SortedContainers.SortedList α) (value : α) : Nat :=
-- !benchmark @start code def=sortedListCount
  let lo := bisectLeftGo s0 value 0 s0.length
  let hi := bisectRightGo s0 value 0 s0.length
  hi - lo
-- !benchmark @end code def=sortedListCount

-- !benchmark @start code_aux def=sortedListIndex
-- !benchmark @end code_aux def=sortedListIndex

-- Python raises ValueError if not found in [start, stop); Lean returns stop.
def SortedContainers.SortedList.index (s0 : SortedContainers.SortedList α) (value : α) (start stop : Nat) : Nat :=
-- !benchmark @start code def=sortedListIndex
  let lo := bisectLeftGo s0 value 0 s0.length
  if lo >= start && lo < stop && (s0[lo]? == some value)
  then lo
  else stop
-- !benchmark @end code def=sortedListIndex

-- !benchmark @start code_aux def=sortedListClear
-- !benchmark @end code_aux def=sortedListClear

def SortedContainers.SortedList.clear (_ : SortedContainers.SortedList α) : SortedContainers.SortedList α :=
-- !benchmark @start code def=sortedListClear
  []
-- !benchmark @end code def=sortedListClear

-- !benchmark @start code_aux def=sortedListCopy
-- !benchmark @end code_aux def=sortedListCopy

def SortedContainers.SortedList.copy (s0 : SortedContainers.SortedList α) : SortedContainers.SortedList α :=
-- !benchmark @start code def=sortedListCopy
  s0
-- !benchmark @end code def=sortedListCopy

-- !benchmark @start code_aux def=sortedListPop
-- !benchmark @end code_aux def=sortedListPop

-- Python's pop returns the value and removes it in-place. Lean: returns value only.
def SortedContainers.SortedList.pop (s0 : SortedContainers.SortedList α) (index : Nat) : α :=
-- !benchmark @start code def=sortedListPop
  match s0[index]? with
  | some x => x
  | none   => default
-- !benchmark @end code def=sortedListPop

-- !benchmark @start code_aux def=sortedListIrange
-- !benchmark @end code_aux def=sortedListIrange

-- `inclusive=true` → both endpoints inclusive; `inclusive=false` → both exclusive.
-- Python's irange takes a 2-tuple for inclusive; simplified here to one Bool.
def SortedContainers.SortedList.irange (s0 : SortedContainers.SortedList α)
    (minimum maximum : α) (inclusive reverse : Bool) : List α :=
-- !benchmark @start code def=sortedListIrange
  let lo := if inclusive then bisectLeftGo s0 minimum 0 s0.length
            else bisectRightGo s0 minimum 0 s0.length
  let hi := if inclusive then bisectRightGo s0 maximum 0 s0.length
            else bisectLeftGo s0 maximum 0 s0.length
  let result := (s0.take hi).drop lo
  if reverse then result.reverse else result
-- !benchmark @end code def=sortedListIrange

-- !benchmark @start code_aux def=sortedListIslice
-- !benchmark @end code_aux def=sortedListIslice

def SortedContainers.SortedList.islice (s0 : SortedContainers.SortedList α)
    (start stop : Nat) (reverse : Bool) : List α :=
-- !benchmark @start code def=sortedListIslice
  let result := (s0.take stop).drop start
  if reverse then result.reverse else result
-- !benchmark @end code def=sortedListIslice

-- !benchmark @start code_aux def=sortedListIter
-- !benchmark @end code_aux def=sortedListIter

def SortedContainers.SortedList.iter (s0 : SortedContainers.SortedList α) : List α :=
-- !benchmark @start code def=sortedListIter
  s0
-- !benchmark @end code def=sortedListIter

-- !benchmark @start code_aux def=sortedListReversed
-- !benchmark @end code_aux def=sortedListReversed

def SortedContainers.SortedList.reversed (s0 : SortedContainers.SortedList α) : List α :=
-- !benchmark @start code def=sortedListReversed
  s0.reverse
-- !benchmark @end code def=sortedListReversed

-- Dropped APIs (Python-specific or raises NotImplementedError in Python):

-- ── SortedKeyList implementations (LLM task) ───────────────────────────

-- !benchmark @start code_aux def=sortedKeyListMk
-- !benchmark @end code_aux def=sortedKeyListMk

def SortedContainers.SortedKeyList.mk (xs : List α) : SortedContainers.SortedKeyList α :=
-- !benchmark @start code def=sortedKeyListMk
  ordSort xs
-- !benchmark @end code def=sortedKeyListMk

-- !benchmark @start code_aux def=sortedKeyListContains
-- !benchmark @end code_aux def=sortedKeyListContains

def SortedContainers.SortedKeyList.contains (s0 : SortedContainers.SortedKeyList α) (value : α) : Bool :=
-- !benchmark @start code def=sortedKeyListContains
  let pos := bisectLeftGo s0 value 0 s0.length
  match s0[pos]? with
  | some x => x == value
  | none   => false
-- !benchmark @end code def=sortedKeyListContains

-- !benchmark @start code_aux def=sortedKeyListAdd
-- !benchmark @end code_aux def=sortedKeyListAdd

-- Return type is SortedList α (matching benchmark.json signature).
def SortedContainers.SortedKeyList.add (s0 : SortedContainers.SortedKeyList α) (value : α) : SortedContainers.SortedList α :=
-- !benchmark @start code def=sortedKeyListAdd
  sortedInsert s0 value
-- !benchmark @end code def=sortedKeyListAdd

-- !benchmark @start code_aux def=sortedKeyListDiscard
-- !benchmark @end code_aux def=sortedKeyListDiscard

def SortedContainers.SortedKeyList.discard (s0 : SortedContainers.SortedKeyList α) (value : α) : SortedContainers.SortedList α :=
-- !benchmark @start code def=sortedKeyListDiscard
  let pos := bisectLeftGo s0 value 0 s0.length
  match s0[pos]? with
  | some x => if x == value then s0.eraseIdx pos else s0
  | none   => s0
-- !benchmark @end code def=sortedKeyListDiscard

-- !benchmark @start code_aux def=sortedKeyListRemove
-- !benchmark @end code_aux def=sortedKeyListRemove

def SortedContainers.SortedKeyList.remove (s0 : SortedContainers.SortedKeyList α) (value : α) : SortedContainers.SortedList α :=
-- !benchmark @start code def=sortedKeyListRemove
  SortedContainers.SortedKeyList.discard s0 value
-- !benchmark @end code def=sortedKeyListRemove

-- !benchmark @start code_aux def=sortedKeyListBisectLeft
-- !benchmark @end code_aux def=sortedKeyListBisectLeft

def SortedContainers.SortedKeyList.bisect_left (s0 : SortedContainers.SortedKeyList α) (value : α) : Nat :=
-- !benchmark @start code def=sortedKeyListBisectLeft
  bisectLeftGo s0 value 0 s0.length
-- !benchmark @end code def=sortedKeyListBisectLeft

-- !benchmark @start code_aux def=sortedKeyListBisectRight
-- !benchmark @end code_aux def=sortedKeyListBisectRight

def SortedContainers.SortedKeyList.bisect_right (s0 : SortedContainers.SortedKeyList α) (value : α) : Nat :=
-- !benchmark @start code def=sortedKeyListBisectRight
  bisectRightGo s0 value 0 s0.length
-- !benchmark @end code def=sortedKeyListBisectRight

-- !benchmark @start code_aux def=sortedKeyListBisectKeyLeft
-- !benchmark @end code_aux def=sortedKeyListBisectKeyLeft

-- @review human: bisect_key requires a stored key function not present in
-- this Lean model.  Approximate via lexicographic comparison of toString
-- representations; requires [ToString α].
def SortedContainers.SortedKeyList.bisect_key_left [ToString α]
    (s0 : SortedContainers.SortedKeyList α) (key : String) : Nat :=
-- !benchmark @start code def=sortedKeyListBisectKeyLeft
  (s0.map toString).foldl (fun acc k => if k < key then acc + 1 else acc) 0
-- !benchmark @end code def=sortedKeyListBisectKeyLeft

-- !benchmark @start code_aux def=sortedKeyListBisectKeyRight
-- !benchmark @end code_aux def=sortedKeyListBisectKeyRight

-- @review human: same approximation as bisect_key_left.
def SortedContainers.SortedKeyList.bisect_key_right [ToString α]
    (s0 : SortedContainers.SortedKeyList α) (key : String) : Nat :=
-- !benchmark @start code def=sortedKeyListBisectKeyRight
  (s0.map toString).foldl (fun acc k => if k <= key then acc + 1 else acc) 0
-- !benchmark @end code def=sortedKeyListBisectKeyRight

-- !benchmark @start code_aux def=sortedKeyListCount
-- !benchmark @end code_aux def=sortedKeyListCount

def SortedContainers.SortedKeyList.count (s0 : SortedContainers.SortedKeyList α) (value : α) : Nat :=
-- !benchmark @start code def=sortedKeyListCount
  let lo := bisectLeftGo s0 value 0 s0.length
  let hi := bisectRightGo s0 value 0 s0.length
  hi - lo
-- !benchmark @end code def=sortedKeyListCount

-- !benchmark @start code_aux def=sortedKeyListIndex
-- !benchmark @end code_aux def=sortedKeyListIndex

-- Python raises ValueError if not found in [start, stop); Lean returns stop.
def SortedContainers.SortedKeyList.index (s0 : SortedContainers.SortedKeyList α) (value : α) (start stop : Nat) : Nat :=
-- !benchmark @start code def=sortedKeyListIndex
  let lo := bisectLeftGo s0 value 0 s0.length
  if lo >= start && lo < stop && (s0[lo]? == some value)
  then lo
  else stop
-- !benchmark @end code def=sortedKeyListIndex

-- !benchmark @start code_aux def=sortedKeyListIrange
-- !benchmark @end code_aux def=sortedKeyListIrange

def SortedContainers.SortedKeyList.irange (s0 : SortedContainers.SortedKeyList α)
    (minimum maximum : α) (inclusive reverse : Bool) : List α :=
-- !benchmark @start code def=sortedKeyListIrange
  let lo := if inclusive then bisectLeftGo s0 minimum 0 s0.length
            else bisectRightGo s0 minimum 0 s0.length
  let hi := if inclusive then bisectRightGo s0 maximum 0 s0.length
            else bisectLeftGo s0 maximum 0 s0.length
  let result := (s0.take hi).drop lo
  if reverse then result.reverse else result
-- !benchmark @end code def=sortedKeyListIrange

-- !benchmark @start code_aux def=sortedKeyListIrangeKey
-- !benchmark @end code_aux def=sortedKeyListIrangeKey

-- @review human: irange_key uses the stored key function; modelled as irange
-- on value order (no key function stored in this Lean model).
def SortedContainers.SortedKeyList.irange_key (s0 : SortedContainers.SortedKeyList α)
    (min_key max_key : α) (inclusive reverse : Bool) : List α :=
-- !benchmark @start code def=sortedKeyListIrangeKey
  SortedContainers.SortedKeyList.irange s0 min_key max_key inclusive reverse
-- !benchmark @end code def=sortedKeyListIrangeKey

-- !benchmark @start code_aux def=sortedKeyListClear
-- !benchmark @end code_aux def=sortedKeyListClear

def SortedContainers.SortedKeyList.clear (_ : SortedContainers.SortedKeyList α) : SortedContainers.SortedList α :=
-- !benchmark @start code def=sortedKeyListClear
  []
-- !benchmark @end code def=sortedKeyListClear

-- !benchmark @start code_aux def=sortedKeyListCopy
-- !benchmark @end code_aux def=sortedKeyListCopy

def SortedContainers.SortedKeyList.copy (s0 : SortedContainers.SortedKeyList α) : SortedContainers.SortedList α :=
-- !benchmark @start code def=sortedKeyListCopy
  s0
-- !benchmark @end code def=sortedKeyListCopy

-- !benchmark @start code_aux def=sortedKeyListUpdate
-- !benchmark @end code_aux def=sortedKeyListUpdate

def SortedContainers.SortedKeyList.update (s0 : SortedContainers.SortedKeyList α) (iterable : List α) : SortedContainers.SortedList α :=
-- !benchmark @start code def=sortedKeyListUpdate
  ordSort (s0 ++ iterable)
-- !benchmark @end code def=sortedKeyListUpdate

-- Dropped APIs:
