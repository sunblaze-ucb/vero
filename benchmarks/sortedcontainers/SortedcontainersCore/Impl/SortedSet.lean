import SortedcontainersCore.Impl.SortedList

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# SortedcontainersCore.Impl.SortedSet

Pure-functional Lean 4 model of Python's `SortedSet` from the
`sortedcontainers` library.  Modelled as a sorted `List α` with no
duplicate values.

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
Implement only the function bodies.
-/

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- ── Types (no markers — fixed vocabulary) ──────────────────────────────

/-- A sorted set.  Values are maintained in ascending order with no
    duplicates.  Modelled as `List α` in Lean. -/
abbrev SortedContainers.SortedSet (α : Type) := List α

-- ── Variable declaration ────────────────────────────────────────────────
variable {α : Type} [Ord α] [BEq α] [Inhabited α]

-- ── Sig abbrevs (no markers — fixed vocabulary) ─────────────────────────

namespace SortedContainers

abbrev SortedSetMkSig                      := List α → SortedSet α
abbrev SortedSetContainsSig                := SortedSet α → α → Bool
abbrev SortedSetLenSig                     := SortedSet α → Nat
abbrev SortedSetGetitemSig                 := SortedSet α → Nat → α
abbrev SortedSetDelitemSig                 := SortedSet α → Nat → SortedSet α
abbrev SortedSetAddSig                     := SortedSet α → α → SortedSet α
abbrev SortedSetDiscardSig                 := SortedSet α → α → SortedSet α
abbrev SortedSetRemoveSig                  := SortedSet α → α → SortedSet α
abbrev SortedSetCountSig                   := SortedSet α → α → Nat
abbrev SortedSetClearSig                   := SortedSet α → SortedSet α
abbrev SortedSetCopySig                    := SortedSet α → SortedSet α
abbrev SortedSetPopSig                     := SortedSet α → Nat → α
abbrev SortedSetIterSig                    := SortedSet α → List α
abbrev SortedSetReversedSig                := SortedSet α → List α
abbrev SortedSetDifferenceSig              := SortedSet α → SortedSet α → SortedSet α
abbrev SortedSetDifferenceUpdateSig        := SortedSet α → SortedSet α → SortedSet α
abbrev SortedSetIntersectionSig            := SortedSet α → SortedSet α → SortedSet α
abbrev SortedSetIntersectionUpdateSig      := SortedSet α → SortedSet α → SortedSet α
abbrev SortedSetSymmetricDifferenceSig     := SortedSet α → SortedSet α → SortedSet α
abbrev SortedSetSymmetricDifferenceUpdateSig := SortedSet α → SortedSet α → SortedSet α
abbrev SortedSetUnionSig                   := SortedSet α → SortedSet α → SortedSet α
abbrev SortedSetUpdateSig                  := SortedSet α → SortedSet α → SortedSet α

end SortedContainers

-- ── Private helper: dedup a sorted list ────────────────────────────────

private def sortedDedup (lst : List α) : List α :=
  match lst with
  | [] => []
  | [x] => [x]
  | x :: y :: rest =>
    if x == y then sortedDedup (y :: rest)
    else x :: sortedDedup (y :: rest)

/-- Build a SortedSet from a list: sort then dedup. -/
private def buildSortedSet (lst : List α) : SortedContainers.SortedSet α :=
  sortedDedup (ordSort lst)

-- ── SortedSet implementations (LLM task) ───────────────────────────────

-- !benchmark @start code_aux def=sortedSetMk
-- !benchmark @end code_aux def=sortedSetMk

def SortedContainers.SortedSet.mk (xs : List α) : SortedContainers.SortedSet α :=
-- !benchmark @start code def=sortedSetMk
  buildSortedSet xs
-- !benchmark @end code def=sortedSetMk

-- !benchmark @start code_aux def=sortedSetContains
-- !benchmark @end code_aux def=sortedSetContains

def SortedContainers.SortedSet.contains (s0 : SortedContainers.SortedSet α) (value : α) : Bool :=
-- !benchmark @start code def=sortedSetContains
  let pos := bisectLeftGo s0 value 0 s0.length
  match s0[pos]? with
  | some x => x == value
  | none   => false
-- !benchmark @end code def=sortedSetContains

-- !benchmark @start code_aux def=sortedSetLen
-- !benchmark @end code_aux def=sortedSetLen

def SortedContainers.SortedSet.len (s0 : SortedContainers.SortedSet α) : Nat :=
-- !benchmark @start code def=sortedSetLen
  s0.length
-- !benchmark @end code def=sortedSetLen

-- !benchmark @start code_aux def=sortedSetGetitem
-- !benchmark @end code_aux def=sortedSetGetitem

def SortedContainers.SortedSet.getitem (s0 : SortedContainers.SortedSet α) (index : Nat) : α :=
-- !benchmark @start code def=sortedSetGetitem
  match s0[index]? with
  | some x => x
  | none   => default
-- !benchmark @end code def=sortedSetGetitem

-- !benchmark @start code_aux def=sortedSetDelitem
-- !benchmark @end code_aux def=sortedSetDelitem

def SortedContainers.SortedSet.delitem (s0 : SortedContainers.SortedSet α) (index : Nat) : SortedContainers.SortedSet α :=
-- !benchmark @start code def=sortedSetDelitem
  s0.eraseIdx index
-- !benchmark @end code def=sortedSetDelitem

-- !benchmark @start code_aux def=sortedSetAdd
-- !benchmark @end code_aux def=sortedSetAdd

def SortedContainers.SortedSet.add (s0 : SortedContainers.SortedSet α) (value : α) : SortedContainers.SortedSet α :=
-- !benchmark @start code def=sortedSetAdd
  if SortedContainers.SortedSet.contains s0 value then s0
  else sortedInsert s0 value
-- !benchmark @end code def=sortedSetAdd

-- !benchmark @start code_aux def=sortedSetDiscard
-- !benchmark @end code_aux def=sortedSetDiscard

def SortedContainers.SortedSet.discard (s0 : SortedContainers.SortedSet α) (value : α) : SortedContainers.SortedSet α :=
-- !benchmark @start code def=sortedSetDiscard
  let pos := bisectLeftGo s0 value 0 s0.length
  match s0[pos]? with
  | some x => if x == value then s0.eraseIdx pos else s0
  | none   => s0
-- !benchmark @end code def=sortedSetDiscard

-- !benchmark @start code_aux def=sortedSetRemove
-- !benchmark @end code_aux def=sortedSetRemove

-- Python raises KeyError if not found; Lean returns s0 unchanged.
def SortedContainers.SortedSet.remove (s0 : SortedContainers.SortedSet α) (value : α) : SortedContainers.SortedSet α :=
-- !benchmark @start code def=sortedSetRemove
  SortedContainers.SortedSet.discard s0 value
-- !benchmark @end code def=sortedSetRemove

-- !benchmark @start code_aux def=sortedSetCount
-- !benchmark @end code_aux def=sortedSetCount

-- SortedSet has no duplicates, so count is 0 or 1.
def SortedContainers.SortedSet.count (s0 : SortedContainers.SortedSet α) (value : α) : Nat :=
-- !benchmark @start code def=sortedSetCount
  if SortedContainers.SortedSet.contains s0 value then 1 else 0
-- !benchmark @end code def=sortedSetCount

-- !benchmark @start code_aux def=sortedSetClear
-- !benchmark @end code_aux def=sortedSetClear

def SortedContainers.SortedSet.clear (_ : SortedContainers.SortedSet α) : SortedContainers.SortedSet α :=
-- !benchmark @start code def=sortedSetClear
  []
-- !benchmark @end code def=sortedSetClear

-- !benchmark @start code_aux def=sortedSetCopy
-- !benchmark @end code_aux def=sortedSetCopy

def SortedContainers.SortedSet.copy (s0 : SortedContainers.SortedSet α) : SortedContainers.SortedSet α :=
-- !benchmark @start code def=sortedSetCopy
  s0
-- !benchmark @end code def=sortedSetCopy

-- !benchmark @start code_aux def=sortedSetPop
-- !benchmark @end code_aux def=sortedSetPop

-- Python's pop(index) removes and returns the value at index.
-- Lean: returns the value only.
def SortedContainers.SortedSet.pop (s0 : SortedContainers.SortedSet α) (index : Nat) : α :=
-- !benchmark @start code def=sortedSetPop
  match s0[index]? with
  | some x => x
  | none   => default
-- !benchmark @end code def=sortedSetPop

-- !benchmark @start code_aux def=sortedSetIter
-- !benchmark @end code_aux def=sortedSetIter

def SortedContainers.SortedSet.iter (s0 : SortedContainers.SortedSet α) : List α :=
-- !benchmark @start code def=sortedSetIter
  s0
-- !benchmark @end code def=sortedSetIter

-- !benchmark @start code_aux def=sortedSetReversed
-- !benchmark @end code_aux def=sortedSetReversed

def SortedContainers.SortedSet.reversed (s0 : SortedContainers.SortedSet α) : List α :=
-- !benchmark @start code def=sortedSetReversed
  s0.reverse
-- !benchmark @end code def=sortedSetReversed

-- !benchmark @start code_aux def=sortedSetDifference
-- !benchmark @end code_aux def=sortedSetDifference

-- @review human: benchmark.json has `iterables: α` for the second param; changed to
-- `SortedSet α` for correct set-difference semantics.
def SortedContainers.SortedSet.difference (s0 other : SortedContainers.SortedSet α) : SortedContainers.SortedSet α :=
-- !benchmark @start code def=sortedSetDifference
  s0.filter (fun x => !SortedContainers.SortedSet.contains other x)
-- !benchmark @end code def=sortedSetDifference

-- !benchmark @start code_aux def=sortedSetDifferenceUpdate
-- !benchmark @end code_aux def=sortedSetDifferenceUpdate

def SortedContainers.SortedSet.difference_update (s0 other : SortedContainers.SortedSet α) : SortedContainers.SortedSet α :=
-- !benchmark @start code def=sortedSetDifferenceUpdate
  SortedContainers.SortedSet.difference s0 other
-- !benchmark @end code def=sortedSetDifferenceUpdate

-- !benchmark @start code_aux def=sortedSetIntersection
-- !benchmark @end code_aux def=sortedSetIntersection

def SortedContainers.SortedSet.intersection (s0 other : SortedContainers.SortedSet α) : SortedContainers.SortedSet α :=
-- !benchmark @start code def=sortedSetIntersection
  s0.filter (fun x => SortedContainers.SortedSet.contains other x)
-- !benchmark @end code def=sortedSetIntersection

-- !benchmark @start code_aux def=sortedSetIntersectionUpdate
-- !benchmark @end code_aux def=sortedSetIntersectionUpdate

def SortedContainers.SortedSet.intersection_update (s0 other : SortedContainers.SortedSet α) : SortedContainers.SortedSet α :=
-- !benchmark @start code def=sortedSetIntersectionUpdate
  SortedContainers.SortedSet.intersection s0 other
-- !benchmark @end code def=sortedSetIntersectionUpdate

-- !benchmark @start code_aux def=sortedSetSymmetricDifference
-- !benchmark @end code_aux def=sortedSetSymmetricDifference

def SortedContainers.SortedSet.symmetric_difference (s0 other : SortedContainers.SortedSet α) : SortedContainers.SortedSet α :=
-- !benchmark @start code def=sortedSetSymmetricDifference
  let inS0NotOther := s0.filter (fun x => !SortedContainers.SortedSet.contains other x)
  let inOtherNotS0 := other.filter (fun x => !SortedContainers.SortedSet.contains s0 x)
  buildSortedSet (inS0NotOther ++ inOtherNotS0)
-- !benchmark @end code def=sortedSetSymmetricDifference

-- !benchmark @start code_aux def=sortedSetSymmetricDifferenceUpdate
-- !benchmark @end code_aux def=sortedSetSymmetricDifferenceUpdate

def SortedContainers.SortedSet.symmetric_difference_update (s0 other : SortedContainers.SortedSet α) : SortedContainers.SortedSet α :=
-- !benchmark @start code def=sortedSetSymmetricDifferenceUpdate
  SortedContainers.SortedSet.symmetric_difference s0 other
-- !benchmark @end code def=sortedSetSymmetricDifferenceUpdate

-- !benchmark @start code_aux def=sortedSetUnion
-- !benchmark @end code_aux def=sortedSetUnion

def SortedContainers.SortedSet.union (s0 other : SortedContainers.SortedSet α) : SortedContainers.SortedSet α :=
-- !benchmark @start code def=sortedSetUnion
  let combined := s0 ++ other.filter (fun x => !SortedContainers.SortedSet.contains s0 x)
  buildSortedSet combined
-- !benchmark @end code def=sortedSetUnion

-- !benchmark @start code_aux def=sortedSetUpdate
-- !benchmark @end code_aux def=sortedSetUpdate

-- @review human: benchmark.json has `iterables: α`; changed to `SortedSet α` for
-- correct semantics.
def SortedContainers.SortedSet.update (s0 other : SortedContainers.SortedSet α) : SortedContainers.SortedSet α :=
-- !benchmark @start code def=sortedSetUpdate
  SortedContainers.SortedSet.union s0 other
-- !benchmark @end code def=sortedSetUpdate

-- Dropped APIs:
