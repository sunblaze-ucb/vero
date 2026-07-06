import SortedcontainersCore.Impl.SortedList

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# SortedcontainersCore.Impl.SortedDict

Pure-functional Lean 4 model of Python's `SortedDict` from the
`sortedcontainers` library.  Modelled as a sorted `List (α × β)` with
keys in ascending `Ord` order (no duplicate keys).

View types (`SortedKeysView`, `SortedItemsView`, `SortedValuesView`)
are dropped since `keys`, `items`, and `values` return plain `List`
in this model.

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
Implement only the function bodies.
-/

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- ── Types (no markers — fixed vocabulary) ──────────────────────────────

/-- A sorted dictionary.  Keys are maintained in ascending `Ord` order
    with no duplicates.  Modelled as `List (α × β)` in Lean. -/
abbrev SortedContainers.SortedDict (α β : Type) := List (α × β)

-- Dropped view types (Python-specific dict-view objects):

-- ── Variable declaration ────────────────────────────────────────────────
variable {α β : Type} [Ord α] [BEq α] [Inhabited α] [Inhabited β]

-- ── Sig abbrevs (no markers — fixed vocabulary) ─────────────────────────

namespace SortedContainers

abbrev SortedDictMkSig         := List (α × β) → SortedDict α β
abbrev SortedDictDelitemSig    := SortedDict α β → α → SortedDict α β
abbrev SortedDictSetitemSig    := SortedDict α β → α → β → SortedDict α β
abbrev SortedDictIterSig       := SortedDict α β → List α
abbrev SortedDictReversedSig   := SortedDict α β → List α
abbrev SortedDictClearSig      := SortedDict α β → SortedDict α β
abbrev SortedDictCopySig       := SortedDict α β → SortedDict α β
abbrev SortedDictItemsSig      := SortedDict α β → List (α × β)
abbrev SortedDictKeysSig       := SortedDict α β → List α
abbrev SortedDictValuesSig     := SortedDict α β → List β
abbrev SortedDictPopSig        := SortedDict α β → α → β → β
abbrev SortedDictPopitemSig    := SortedDict α β → Nat → (α × β)
abbrev SortedDictPeekitemSig   := SortedDict α β → Nat → (α × β)
abbrev SortedDictSetdefaultSig := SortedDict α β → α → β → SortedDict α β

end SortedContainers

-- ── Private helpers ─────────────────────────────────────────────────────

/-- Sort a list of pairs by key using `Ord`. -/
private def sortByKey (lst : List (α × β)) : List (α × β) :=
  (lst.toArray.qsort (fun a b => Ord.compare a.1 b.1 == Ordering.lt)).toList

/-- Insert or update a key-value pair, maintaining sorted key order. -/
private def dictInsert (lst : List (α × β)) (key : α) (val : β) : List (α × β) :=
  let without := lst.filter (fun p => !(p.1 == key))
  let pos := bisectRightGo (without.map Prod.fst) key 0 without.length
  without.take pos ++ [(key, val)] ++ without.drop pos

/-- Find a value by key. -/
private def dictFind (lst : List (α × β)) (key : α) : Option β :=
  (lst.find? (fun p => p.1 == key)).map Prod.snd

-- ── SortedDict implementations (LLM task) ──────────────────────────────

-- !benchmark @start code_aux def=sortedDictMk
-- !benchmark @end code_aux def=sortedDictMk

-- Builds a sorted dict from a list of pairs: later duplicates win, result sorted.
def SortedContainers.SortedDict.mk (pairs : List (α × β)) : SortedContainers.SortedDict α β :=
-- !benchmark @start code def=sortedDictMk
  let deduped := pairs.foldl (fun acc p => dictInsert acc p.1 p.2) []
  sortByKey deduped
-- !benchmark @end code def=sortedDictMk

-- !benchmark @start code_aux def=sortedDictDelitem
-- !benchmark @end code_aux def=sortedDictDelitem

def SortedContainers.SortedDict.delitem (s0 : SortedContainers.SortedDict α β) (key : α) : SortedContainers.SortedDict α β :=
-- !benchmark @start code def=sortedDictDelitem
  s0.filter (fun p => !(p.1 == key))
-- !benchmark @end code def=sortedDictDelitem

-- !benchmark @start code_aux def=sortedDictSetitem
-- !benchmark @end code_aux def=sortedDictSetitem

def SortedContainers.SortedDict.setitem (s0 : SortedContainers.SortedDict α β) (key : α) (value : β) : SortedContainers.SortedDict α β :=
-- !benchmark @start code def=sortedDictSetitem
  dictInsert s0 key value
-- !benchmark @end code def=sortedDictSetitem

-- !benchmark @start code_aux def=sortedDictIter
-- !benchmark @end code_aux def=sortedDictIter

def SortedContainers.SortedDict.iter (s0 : SortedContainers.SortedDict α β) : List α :=
-- !benchmark @start code def=sortedDictIter
  s0.map Prod.fst
-- !benchmark @end code def=sortedDictIter

-- !benchmark @start code_aux def=sortedDictReversed
-- !benchmark @end code_aux def=sortedDictReversed

def SortedContainers.SortedDict.reversed (s0 : SortedContainers.SortedDict α β) : List α :=
-- !benchmark @start code def=sortedDictReversed
  (s0.map Prod.fst).reverse
-- !benchmark @end code def=sortedDictReversed

-- !benchmark @start code_aux def=sortedDictClear
-- !benchmark @end code_aux def=sortedDictClear

def SortedContainers.SortedDict.clear (_ : SortedContainers.SortedDict α β) : SortedContainers.SortedDict α β :=
-- !benchmark @start code def=sortedDictClear
  []
-- !benchmark @end code def=sortedDictClear

-- !benchmark @start code_aux def=sortedDictCopy
-- !benchmark @end code_aux def=sortedDictCopy

def SortedContainers.SortedDict.copy (s0 : SortedContainers.SortedDict α β) : SortedContainers.SortedDict α β :=
-- !benchmark @start code def=sortedDictCopy
  s0
-- !benchmark @end code def=sortedDictCopy

-- !benchmark @start code_aux def=sortedDictItems
-- !benchmark @end code_aux def=sortedDictItems

def SortedContainers.SortedDict.items (s0 : SortedContainers.SortedDict α β) : List (α × β) :=
-- !benchmark @start code def=sortedDictItems
  s0
-- !benchmark @end code def=sortedDictItems

-- !benchmark @start code_aux def=sortedDictKeys
-- !benchmark @end code_aux def=sortedDictKeys

def SortedContainers.SortedDict.keys (s0 : SortedContainers.SortedDict α β) : List α :=
-- !benchmark @start code def=sortedDictKeys
  s0.map Prod.fst
-- !benchmark @end code def=sortedDictKeys

-- !benchmark @start code_aux def=sortedDictValues
-- !benchmark @end code_aux def=sortedDictValues

def SortedContainers.SortedDict.values (s0 : SortedContainers.SortedDict α β) : List β :=
-- !benchmark @start code def=sortedDictValues
  s0.map Prod.snd
-- !benchmark @end code def=sortedDictValues

-- !benchmark @start code_aux def=sortedDictPop
-- !benchmark @end code_aux def=sortedDictPop

-- Returns the value for `key` if present, else `default`.
-- Python removes the key; Lean: returns value only.
def SortedContainers.SortedDict.pop (s0 : SortedContainers.SortedDict α β) (key : α) (default : β) : β :=
-- !benchmark @start code def=sortedDictPop
  match dictFind s0 key with
  | some v => v
  | none   => default
-- !benchmark @end code def=sortedDictPop

-- !benchmark @start code_aux def=sortedDictPopitem
-- !benchmark @end code_aux def=sortedDictPopitem

-- Python's popitem(index=-1) removes and returns the item at index.
-- Lean: returns the item only (Inhabited fallback for out-of-bounds).
def SortedContainers.SortedDict.popitem (s0 : SortedContainers.SortedDict α β) (index : Nat) : (α × β) :=
-- !benchmark @start code def=sortedDictPopitem
  match s0[index]? with
  | some p => p
  | none   => (default, default)
-- !benchmark @end code def=sortedDictPopitem

-- !benchmark @start code_aux def=sortedDictPeekitem
-- !benchmark @end code_aux def=sortedDictPeekitem

def SortedContainers.SortedDict.peekitem (s0 : SortedContainers.SortedDict α β) (index : Nat) : (α × β) :=
-- !benchmark @start code def=sortedDictPeekitem
  match s0[index]? with
  | some p => p
  | none   => (default, default)
-- !benchmark @end code def=sortedDictPeekitem

-- !benchmark @start code_aux def=sortedDictSetdefault
-- !benchmark @end code_aux def=sortedDictSetdefault

-- If key is already present, return dict unchanged.
-- Otherwise, insert (key, default) and return the updated dict.
def SortedContainers.SortedDict.setdefault (s0 : SortedContainers.SortedDict α β) (key : α) (dflt : β) : SortedContainers.SortedDict α β :=
-- !benchmark @start code def=sortedDictSetdefault
  match dictFind s0 key with
  | some _ => s0
  | none   => dictInsert s0 key dflt
-- !benchmark @end code def=sortedDictSetdefault

-- Dropped APIs:
