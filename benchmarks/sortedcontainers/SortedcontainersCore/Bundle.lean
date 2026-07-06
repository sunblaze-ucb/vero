import SortedcontainersCore.Impl.SortedList
import SortedcontainersCore.Impl.SortedSet
import SortedcontainersCore.Impl.SortedDict

/-!
# SortedcontainersCore.Bundle

Per-package implementation bundle for the `SortedcontainersCore` root package.
Collects all API signatures into one structure.

DO NOT MODIFY — benchmark infrastructure.
-/

/-- Bundle collecting all API implementations for the SortedcontainersCore package. -/
structure SortedcontainersCoreBundle where
  -- ── SortedList APIs ──────────────────────────────────────────────────
  sortedListMk          : ∀ {α : Type} [Ord α] [BEq α] [Inhabited α], List α → SortedContainers.SortedList α
  sortedListContains    : ∀ {α : Type} [Ord α] [BEq α] [Inhabited α], SortedContainers.SortedList α → α → Bool
  sortedListLen         : ∀ {α : Type} [Ord α] [BEq α] [Inhabited α], SortedContainers.SortedList α → Nat
  sortedListGetitem     : ∀ {α : Type} [Ord α] [BEq α] [Inhabited α], SortedContainers.SortedList α → Nat → α
  sortedListDelitem     : ∀ {α : Type} [Ord α] [BEq α] [Inhabited α], SortedContainers.SortedList α → Nat → SortedContainers.SortedList α
  sortedListAdd         : ∀ {α : Type} [Ord α] [BEq α] [Inhabited α], SortedContainers.SortedList α → α → SortedContainers.SortedList α
  sortedListDiscard     : ∀ {α : Type} [Ord α] [BEq α] [Inhabited α], SortedContainers.SortedList α → α → SortedContainers.SortedList α
  sortedListRemove      : ∀ {α : Type} [Ord α] [BEq α] [Inhabited α], SortedContainers.SortedList α → α → SortedContainers.SortedList α
  sortedListUpdate      : ∀ {α : Type} [Ord α] [BEq α] [Inhabited α], SortedContainers.SortedList α → List α → SortedContainers.SortedList α
  sortedListExtend      : ∀ {α : Type} [Ord α] [BEq α] [Inhabited α], SortedContainers.SortedList α → List α → SortedContainers.SortedList α
  sortedListBisectLeft  : ∀ {α : Type} [Ord α] [BEq α] [Inhabited α], SortedContainers.SortedList α → α → Nat
  sortedListBisectRight : ∀ {α : Type} [Ord α] [BEq α] [Inhabited α], SortedContainers.SortedList α → α → Nat
  sortedListCount       : ∀ {α : Type} [Ord α] [BEq α] [Inhabited α], SortedContainers.SortedList α → α → Nat
  sortedListIndex       : ∀ {α : Type} [Ord α] [BEq α] [Inhabited α], SortedContainers.SortedList α → α → Nat → Nat → Nat
  sortedListClear       : ∀ {α : Type} [Ord α] [BEq α] [Inhabited α], SortedContainers.SortedList α → SortedContainers.SortedList α
  sortedListCopy        : ∀ {α : Type} [Ord α] [BEq α] [Inhabited α], SortedContainers.SortedList α → SortedContainers.SortedList α
  sortedListPop         : ∀ {α : Type} [Ord α] [BEq α] [Inhabited α], SortedContainers.SortedList α → Nat → α
  sortedListIrange      : ∀ {α : Type} [Ord α] [BEq α] [Inhabited α], SortedContainers.SortedList α → α → α → Bool → Bool → List α
  sortedListIslice      : ∀ {α : Type} [Ord α] [BEq α] [Inhabited α], SortedContainers.SortedList α → Nat → Nat → Bool → List α
  sortedListIter        : ∀ {α : Type} [Ord α] [BEq α] [Inhabited α], SortedContainers.SortedList α → List α
  sortedListReversed    : ∀ {α : Type} [Ord α] [BEq α] [Inhabited α], SortedContainers.SortedList α → List α
  -- ── SortedKeyList APIs ───────────────────────────────────────────────
  sortedKeyListMk           : ∀ {α : Type} [Ord α] [BEq α] [Inhabited α], List α → SortedContainers.SortedKeyList α
  sortedKeyListContains     : ∀ {α : Type} [Ord α] [BEq α] [Inhabited α], SortedContainers.SortedKeyList α → α → Bool
  sortedKeyListAdd          : ∀ {α : Type} [Ord α] [BEq α] [Inhabited α], SortedContainers.SortedKeyList α → α → SortedContainers.SortedList α
  sortedKeyListDiscard      : ∀ {α : Type} [Ord α] [BEq α] [Inhabited α], SortedContainers.SortedKeyList α → α → SortedContainers.SortedList α
  sortedKeyListRemove       : ∀ {α : Type} [Ord α] [BEq α] [Inhabited α], SortedContainers.SortedKeyList α → α → SortedContainers.SortedList α
  sortedKeyListBisectLeft   : ∀ {α : Type} [Ord α] [BEq α] [Inhabited α], SortedContainers.SortedKeyList α → α → Nat
  sortedKeyListBisectRight  : ∀ {α : Type} [Ord α] [BEq α] [Inhabited α], SortedContainers.SortedKeyList α → α → Nat
  sortedKeyListCount        : ∀ {α : Type} [Ord α] [BEq α] [Inhabited α], SortedContainers.SortedKeyList α → α → Nat
  sortedKeyListIndex        : ∀ {α : Type} [Ord α] [BEq α] [Inhabited α], SortedContainers.SortedKeyList α → α → Nat → Nat → Nat
  sortedKeyListIrange       : ∀ {α : Type} [Ord α] [BEq α] [Inhabited α], SortedContainers.SortedKeyList α → α → α → Bool → Bool → List α
  sortedKeyListIrangeKey    : ∀ {α : Type} [Ord α] [BEq α] [Inhabited α], SortedContainers.SortedKeyList α → α → α → Bool → Bool → List α
  sortedKeyListClear        : ∀ {α : Type} [Ord α] [BEq α] [Inhabited α], SortedContainers.SortedKeyList α → SortedContainers.SortedList α
  sortedKeyListCopy         : ∀ {α : Type} [Ord α] [BEq α] [Inhabited α], SortedContainers.SortedKeyList α → SortedContainers.SortedList α
  sortedKeyListUpdate       : ∀ {α : Type} [Ord α] [BEq α] [Inhabited α], SortedContainers.SortedKeyList α → List α → SortedContainers.SortedList α
  -- ── SortedSet APIs ───────────────────────────────────────────────────
  sortedSetMk                        : ∀ {α : Type} [Ord α] [BEq α] [Inhabited α], List α → SortedContainers.SortedSet α
  sortedSetContains                  : ∀ {α : Type} [Ord α] [BEq α] [Inhabited α], SortedContainers.SortedSet α → α → Bool
  sortedSetLen                       : ∀ {α : Type} [Ord α] [BEq α] [Inhabited α], SortedContainers.SortedSet α → Nat
  sortedSetGetitem                   : ∀ {α : Type} [Ord α] [BEq α] [Inhabited α], SortedContainers.SortedSet α → Nat → α
  sortedSetDelitem                   : ∀ {α : Type} [Ord α] [BEq α] [Inhabited α], SortedContainers.SortedSet α → Nat → SortedContainers.SortedSet α
  sortedSetAdd                       : ∀ {α : Type} [Ord α] [BEq α] [Inhabited α], SortedContainers.SortedSet α → α → SortedContainers.SortedSet α
  sortedSetDiscard                   : ∀ {α : Type} [Ord α] [BEq α] [Inhabited α], SortedContainers.SortedSet α → α → SortedContainers.SortedSet α
  sortedSetRemove                    : ∀ {α : Type} [Ord α] [BEq α] [Inhabited α], SortedContainers.SortedSet α → α → SortedContainers.SortedSet α
  sortedSetCount                     : ∀ {α : Type} [Ord α] [BEq α] [Inhabited α], SortedContainers.SortedSet α → α → Nat
  sortedSetClear                     : ∀ {α : Type} [Ord α] [BEq α] [Inhabited α], SortedContainers.SortedSet α → SortedContainers.SortedSet α
  sortedSetCopy                      : ∀ {α : Type} [Ord α] [BEq α] [Inhabited α], SortedContainers.SortedSet α → SortedContainers.SortedSet α
  sortedSetPop                       : ∀ {α : Type} [Ord α] [BEq α] [Inhabited α], SortedContainers.SortedSet α → Nat → α
  sortedSetIter                      : ∀ {α : Type} [Ord α] [BEq α] [Inhabited α], SortedContainers.SortedSet α → List α
  sortedSetReversed                  : ∀ {α : Type} [Ord α] [BEq α] [Inhabited α], SortedContainers.SortedSet α → List α
  sortedSetDifference                : ∀ {α : Type} [Ord α] [BEq α] [Inhabited α], SortedContainers.SortedSet α → SortedContainers.SortedSet α → SortedContainers.SortedSet α
  sortedSetDifferenceUpdate          : ∀ {α : Type} [Ord α] [BEq α] [Inhabited α], SortedContainers.SortedSet α → SortedContainers.SortedSet α → SortedContainers.SortedSet α
  sortedSetIntersection              : ∀ {α : Type} [Ord α] [BEq α] [Inhabited α], SortedContainers.SortedSet α → SortedContainers.SortedSet α → SortedContainers.SortedSet α
  sortedSetIntersectionUpdate        : ∀ {α : Type} [Ord α] [BEq α] [Inhabited α], SortedContainers.SortedSet α → SortedContainers.SortedSet α → SortedContainers.SortedSet α
  sortedSetSymmetricDifference       : ∀ {α : Type} [Ord α] [BEq α] [Inhabited α], SortedContainers.SortedSet α → SortedContainers.SortedSet α → SortedContainers.SortedSet α
  sortedSetSymmetricDifferenceUpdate : ∀ {α : Type} [Ord α] [BEq α] [Inhabited α], SortedContainers.SortedSet α → SortedContainers.SortedSet α → SortedContainers.SortedSet α
  sortedSetUnion                     : ∀ {α : Type} [Ord α] [BEq α] [Inhabited α], SortedContainers.SortedSet α → SortedContainers.SortedSet α → SortedContainers.SortedSet α
  sortedSetUpdate                    : ∀ {α : Type} [Ord α] [BEq α] [Inhabited α], SortedContainers.SortedSet α → SortedContainers.SortedSet α → SortedContainers.SortedSet α
  -- ── SortedDict APIs ──────────────────────────────────────────────────
  sortedDictMk         : ∀ {α β : Type} [Ord α] [BEq α] [Inhabited α] [Inhabited β], List (α × β) → SortedContainers.SortedDict α β
  sortedDictDelitem    : ∀ {α β : Type} [Ord α] [BEq α] [Inhabited α] [Inhabited β], SortedContainers.SortedDict α β → α → SortedContainers.SortedDict α β
  sortedDictSetitem    : ∀ {α β : Type} [Ord α] [BEq α] [Inhabited α] [Inhabited β], SortedContainers.SortedDict α β → α → β → SortedContainers.SortedDict α β
  sortedDictIter       : ∀ {α β : Type} [Ord α] [BEq α] [Inhabited α] [Inhabited β], SortedContainers.SortedDict α β → List α
  sortedDictReversed   : ∀ {α β : Type} [Ord α] [BEq α] [Inhabited α] [Inhabited β], SortedContainers.SortedDict α β → List α
  sortedDictClear      : ∀ {α β : Type} [Ord α] [BEq α] [Inhabited α] [Inhabited β], SortedContainers.SortedDict α β → SortedContainers.SortedDict α β
  sortedDictCopy       : ∀ {α β : Type} [Ord α] [BEq α] [Inhabited α] [Inhabited β], SortedContainers.SortedDict α β → SortedContainers.SortedDict α β
  sortedDictItems      : ∀ {α β : Type} [Ord α] [BEq α] [Inhabited α] [Inhabited β], SortedContainers.SortedDict α β → List (α × β)
  sortedDictKeys       : ∀ {α β : Type} [Ord α] [BEq α] [Inhabited α] [Inhabited β], SortedContainers.SortedDict α β → List α
  sortedDictValues     : ∀ {α β : Type} [Ord α] [BEq α] [Inhabited α] [Inhabited β], SortedContainers.SortedDict α β → List β
  sortedDictPop        : ∀ {α β : Type} [Ord α] [BEq α] [Inhabited α] [Inhabited β], SortedContainers.SortedDict α β → α → β → β
  sortedDictPopitem    : ∀ {α β : Type} [Ord α] [BEq α] [Inhabited α] [Inhabited β], SortedContainers.SortedDict α β → Nat → (α × β)
  sortedDictPeekitem   : ∀ {α β : Type} [Ord α] [BEq α] [Inhabited α] [Inhabited β], SortedContainers.SortedDict α β → Nat → (α × β)
  sortedDictSetdefault : ∀ {α β : Type} [Ord α] [BEq α] [Inhabited α] [Inhabited β], SortedContainers.SortedDict α β → α → β → SortedContainers.SortedDict α β
