import SortedcontainersCore.Impl.SortedList
import SortedcontainersCore.Impl.SortedSet
import SortedcontainersCore.Impl.SortedDict
import SortedcontainersCore.Bundle
import SortedcontainersCore.Harness

/-!
# SortedcontainersCore.Test

`#guard` conformance tests. The original raw-`SortedContainers.*`
guards are kept (append-only). Beyond those we exercise every
manifest API via the bundle-qualified path
`canonical.sortedcontainersCore.<api>` so the wiring is also tested.

Each manifest API has ≥3 `#guard` lines covering distinct behaviours
(empty/min input, typical input, edge cases such as duplicates,
out-of-bounds indices, missing values, or boundary comparator
results).
-/

open SortedContainers

-- ── Original raw-API tests (kept as-is) ─────────────────────────────────

#guard SortedList.contains (SortedList.mk [1, 2, 3]) 2 == true
#guard SortedList.contains (SortedList.mk [1, 2, 3]) 4 == false

#guard SortedList.getitem (SortedList.mk [10, 20, 30]) 1 == 20

#guard SortedList.len (SortedList.mk ([] : List Nat)) == 0
#guard SortedList.len (SortedList.mk [1, 2, 3]) == 3

#guard SortedList.bisect_left (SortedList.mk [10, 20, 30]) 15 == 1
#guard SortedList.bisect_left (SortedList.mk [10, 20, 30]) 20 == 1
#guard SortedList.bisect_right (SortedList.mk [10, 20, 30]) 15 == 1
#guard SortedList.bisect_right (SortedList.mk [10, 20, 30]) 20 == 2

#guard SortedSet.contains (SortedSet.mk [1, 2, 3]) 2 == true
#guard SortedSet.contains (SortedSet.mk [1, 2, 3]) 4 == false

#guard SortedSet.len (SortedSet.mk ([] : List Nat)) == 0
#guard SortedSet.len (SortedSet.mk [1, 2, 3]) == 3

#guard SortedDict.items (SortedDict.mk [(1, 10), (2, 20)]) == [(1, 10), (2, 20)]

#guard SortedDict.keys (SortedDict.mk [(1, 10), (2, 20), (3, 30)]) == [1, 2, 3]

#guard SortedDict.peekitem (SortedDict.mk [(1, 10), (2, 20), (3, 30)]) 1 == (2, 20)

#guard SortedDict.pop (SortedDict.mk [(1, 10), (2, 20), (3, 30)]) 2 0 == 20

#guard SortedDict.values (SortedDict.mk [(1, 10), (2, 20), (3, 30)]) == [10, 20, 30]

-- ── Bundle-qualified API tests ──────────────────────────────────────────
-- Helpers: build inputs through the bundle so that mk + downstream API
-- are both exercised in each test.

namespace SortedcontainersCore.Tests
open SortedContainers

abbrev B := canonical.sortedcontainersCore

end SortedcontainersCore.Tests

open SortedcontainersCore.Tests

-- ─────────── SortedList ───────────────────────────────────────────────

-- sortedListMk
#guard B.sortedListMk ([] : List Nat) == ([] : List Nat)
#guard B.sortedListMk [3, 1, 2] == [1, 2, 3]
#guard B.sortedListMk [2, 2, 1, 3, 1] == [1, 1, 2, 2, 3]

-- sortedListContains
#guard B.sortedListContains (B.sortedListMk [1, 2, 3]) 2 == true
#guard B.sortedListContains (B.sortedListMk [1, 2, 3]) 4 == false
#guard B.sortedListContains (B.sortedListMk ([] : List Nat)) 1 == false

-- sortedListLen
#guard B.sortedListLen (B.sortedListMk ([] : List Nat)) == 0
#guard B.sortedListLen (B.sortedListMk [1, 2, 3]) == 3
#guard B.sortedListLen (B.sortedListMk [1, 1, 1]) == 3

-- sortedListGetitem
#guard B.sortedListGetitem (B.sortedListMk [10, 20, 30]) 0 == 10
#guard B.sortedListGetitem (B.sortedListMk [10, 20, 30]) 2 == 30
#guard B.sortedListGetitem (B.sortedListMk ([] : List Nat)) 0 == (default : Nat)

-- sortedListDelitem
#guard B.sortedListDelitem (B.sortedListMk [10, 20, 30]) 1 == [10, 30]
#guard B.sortedListDelitem (B.sortedListMk [10, 20, 30]) 0 == [20, 30]
#guard B.sortedListDelitem (B.sortedListMk [10, 20, 30]) 5 == [10, 20, 30]

-- sortedListAdd
#guard B.sortedListAdd (B.sortedListMk ([] : List Nat)) 5 == [5]
#guard B.sortedListAdd (B.sortedListMk [1, 3, 5]) 2 == [1, 2, 3, 5]
#guard B.sortedListAdd (B.sortedListMk [1, 2, 3]) 2 == [1, 2, 2, 3]

-- sortedListDiscard
#guard B.sortedListDiscard (B.sortedListMk [1, 2, 3]) 2 == [1, 3]
#guard B.sortedListDiscard (B.sortedListMk [1, 2, 3]) 4 == [1, 2, 3]
#guard B.sortedListDiscard (B.sortedListMk [1, 2, 2, 3]) 2 == [1, 2, 3]

-- sortedListRemove
#guard B.sortedListRemove (B.sortedListMk [1, 2, 3]) 2 == [1, 3]
#guard B.sortedListRemove (B.sortedListMk [1, 2, 3]) 99 == [1, 2, 3]
#guard B.sortedListRemove (B.sortedListMk [5]) 5 == ([] : List Nat)

-- sortedListUpdate
#guard B.sortedListUpdate (B.sortedListMk [1, 3, 5]) [2, 4] == [1, 2, 3, 4, 5]
#guard B.sortedListUpdate (B.sortedListMk ([] : List Nat)) [3, 1, 2] == [1, 2, 3]
#guard B.sortedListUpdate (B.sortedListMk [1, 2, 3]) ([] : List Nat) == [1, 2, 3]

-- sortedListExtend
#guard B.sortedListExtend (B.sortedListMk [1, 3, 5]) [2, 4] == [1, 2, 3, 4, 5]
#guard B.sortedListExtend (B.sortedListMk ([] : List Nat)) [3, 1, 2] == [1, 2, 3]
#guard B.sortedListExtend (B.sortedListMk [1, 2, 3]) ([] : List Nat) == [1, 2, 3]

-- sortedListBisectLeft
#guard B.sortedListBisectLeft (B.sortedListMk [10, 20, 30]) 5 == 0
#guard B.sortedListBisectLeft (B.sortedListMk [10, 20, 30]) 20 == 1
#guard B.sortedListBisectLeft (B.sortedListMk [10, 20, 30]) 35 == 3
#guard B.sortedListBisectLeft (B.sortedListMk [1, 2, 2, 2, 3]) 2 == 1

-- sortedListBisectRight
#guard B.sortedListBisectRight (B.sortedListMk [10, 20, 30]) 5 == 0
#guard B.sortedListBisectRight (B.sortedListMk [10, 20, 30]) 20 == 2
#guard B.sortedListBisectRight (B.sortedListMk [10, 20, 30]) 35 == 3
#guard B.sortedListBisectRight (B.sortedListMk [1, 2, 2, 2, 3]) 2 == 4

-- sortedListCount
#guard B.sortedListCount (B.sortedListMk [1, 2, 3]) 2 == 1
#guard B.sortedListCount (B.sortedListMk [1, 2, 3]) 4 == 0
#guard B.sortedListCount (B.sortedListMk [1, 2, 2, 2, 3]) 2 == 3

-- sortedListIndex
#guard B.sortedListIndex (B.sortedListMk [10, 20, 30]) 20 0 3 == 1
#guard B.sortedListIndex (B.sortedListMk [10, 20, 30]) 99 0 3 == 3
#guard B.sortedListIndex (B.sortedListMk [10, 20, 30]) 10 1 3 == 3

-- sortedListClear
#guard B.sortedListClear (B.sortedListMk [1, 2, 3]) == ([] : List Nat)
#guard B.sortedListClear (B.sortedListMk ([] : List Nat)) == ([] : List Nat)
#guard B.sortedListClear (B.sortedListMk [42]) == ([] : List Nat)

-- sortedListCopy
#guard B.sortedListCopy (B.sortedListMk [1, 2, 3]) == [1, 2, 3]
#guard B.sortedListCopy (B.sortedListMk ([] : List Nat)) == ([] : List Nat)
#guard B.sortedListCopy (B.sortedListMk [3, 1, 2]) == [1, 2, 3]

-- sortedListPop
#guard B.sortedListPop (B.sortedListMk [10, 20, 30]) 1 == 20
#guard B.sortedListPop (B.sortedListMk [10, 20, 30]) 0 == 10
#guard B.sortedListPop (B.sortedListMk ([] : List Nat)) 0 == (default : Nat)

-- sortedListIrange
#guard B.sortedListIrange (B.sortedListMk [1, 2, 3, 4, 5]) 2 4 true false == [2, 3, 4]
#guard B.sortedListIrange (B.sortedListMk [1, 2, 3, 4, 5]) 2 4 false false == [3]
#guard B.sortedListIrange (B.sortedListMk [1, 2, 3, 4, 5]) 2 4 true true == [4, 3, 2]

-- sortedListIslice
#guard B.sortedListIslice (B.sortedListMk [1, 2, 3, 4, 5]) 1 3 false == [2, 3]
#guard B.sortedListIslice (B.sortedListMk [1, 2, 3, 4, 5]) 1 3 true == [3, 2]
#guard B.sortedListIslice (B.sortedListMk [1, 2, 3, 4, 5]) 0 5 false == [1, 2, 3, 4, 5]

-- sortedListIter
#guard B.sortedListIter (B.sortedListMk [3, 1, 2]) == [1, 2, 3]
#guard B.sortedListIter (B.sortedListMk ([] : List Nat)) == ([] : List Nat)
#guard B.sortedListIter (B.sortedListMk [1, 1, 1]) == [1, 1, 1]

-- sortedListReversed
#guard B.sortedListReversed (B.sortedListMk [1, 2, 3]) == [3, 2, 1]
#guard B.sortedListReversed (B.sortedListMk ([] : List Nat)) == ([] : List Nat)
#guard B.sortedListReversed (B.sortedListMk [42]) == [42]

-- ─────────── SortedKeyList ────────────────────────────────────────────

-- sortedKeyListMk
#guard B.sortedKeyListMk ([] : List Nat) == ([] : List Nat)
#guard B.sortedKeyListMk [3, 1, 2] == [1, 2, 3]
#guard B.sortedKeyListMk [2, 2, 1, 3, 1] == [1, 1, 2, 2, 3]

-- sortedKeyListContains
#guard B.sortedKeyListContains (B.sortedKeyListMk [1, 2, 3]) 2 == true
#guard B.sortedKeyListContains (B.sortedKeyListMk [1, 2, 3]) 4 == false
#guard B.sortedKeyListContains (B.sortedKeyListMk ([] : List Nat)) 1 == false

-- sortedKeyListAdd
#guard B.sortedKeyListAdd (B.sortedKeyListMk ([] : List Nat)) 5 == [5]
#guard B.sortedKeyListAdd (B.sortedKeyListMk [1, 3, 5]) 2 == [1, 2, 3, 5]
#guard B.sortedKeyListAdd (B.sortedKeyListMk [1, 2, 3]) 2 == [1, 2, 2, 3]

-- sortedKeyListDiscard
#guard B.sortedKeyListDiscard (B.sortedKeyListMk [1, 2, 3]) 2 == [1, 3]
#guard B.sortedKeyListDiscard (B.sortedKeyListMk [1, 2, 3]) 4 == [1, 2, 3]
#guard B.sortedKeyListDiscard (B.sortedKeyListMk [1, 2, 2, 3]) 2 == [1, 2, 3]

-- sortedKeyListRemove
#guard B.sortedKeyListRemove (B.sortedKeyListMk [1, 2, 3]) 2 == [1, 3]
#guard B.sortedKeyListRemove (B.sortedKeyListMk [1, 2, 3]) 99 == [1, 2, 3]
#guard B.sortedKeyListRemove (B.sortedKeyListMk [5]) 5 == ([] : List Nat)

-- sortedKeyListBisectLeft
#guard B.sortedKeyListBisectLeft (B.sortedKeyListMk [10, 20, 30]) 5 == 0
#guard B.sortedKeyListBisectLeft (B.sortedKeyListMk [10, 20, 30]) 20 == 1
#guard B.sortedKeyListBisectLeft (B.sortedKeyListMk [1, 2, 2, 2, 3]) 2 == 1

-- sortedKeyListBisectRight
#guard B.sortedKeyListBisectRight (B.sortedKeyListMk [10, 20, 30]) 5 == 0
#guard B.sortedKeyListBisectRight (B.sortedKeyListMk [10, 20, 30]) 20 == 2
#guard B.sortedKeyListBisectRight (B.sortedKeyListMk [1, 2, 2, 2, 3]) 2 == 4

-- sortedKeyListCount
#guard B.sortedKeyListCount (B.sortedKeyListMk [1, 2, 3]) 2 == 1
#guard B.sortedKeyListCount (B.sortedKeyListMk [1, 2, 3]) 4 == 0
#guard B.sortedKeyListCount (B.sortedKeyListMk [1, 2, 2, 2, 3]) 2 == 3

-- sortedKeyListIndex
#guard B.sortedKeyListIndex (B.sortedKeyListMk [10, 20, 30]) 20 0 3 == 1
#guard B.sortedKeyListIndex (B.sortedKeyListMk [10, 20, 30]) 99 0 3 == 3
#guard B.sortedKeyListIndex (B.sortedKeyListMk [10, 20, 30]) 10 1 3 == 3

-- sortedKeyListIrange
#guard B.sortedKeyListIrange (B.sortedKeyListMk [1, 2, 3, 4, 5]) 2 4 true false == [2, 3, 4]
#guard B.sortedKeyListIrange (B.sortedKeyListMk [1, 2, 3, 4, 5]) 2 4 false false == [3]
#guard B.sortedKeyListIrange (B.sortedKeyListMk [1, 2, 3, 4, 5]) 2 4 true true == [4, 3, 2]

-- sortedKeyListIrangeKey
#guard B.sortedKeyListIrangeKey (B.sortedKeyListMk [1, 2, 3, 4, 5]) 2 4 true false == [2, 3, 4]
#guard B.sortedKeyListIrangeKey (B.sortedKeyListMk [1, 2, 3, 4, 5]) 2 4 false false == [3]
#guard B.sortedKeyListIrangeKey (B.sortedKeyListMk [1, 2, 3, 4, 5]) 2 4 true true == [4, 3, 2]

-- sortedKeyListClear
#guard B.sortedKeyListClear (B.sortedKeyListMk [1, 2, 3]) == ([] : List Nat)
#guard B.sortedKeyListClear (B.sortedKeyListMk ([] : List Nat)) == ([] : List Nat)
#guard B.sortedKeyListClear (B.sortedKeyListMk [42]) == ([] : List Nat)

-- sortedKeyListCopy
#guard B.sortedKeyListCopy (B.sortedKeyListMk [1, 2, 3]) == [1, 2, 3]
#guard B.sortedKeyListCopy (B.sortedKeyListMk ([] : List Nat)) == ([] : List Nat)
#guard B.sortedKeyListCopy (B.sortedKeyListMk [3, 1, 2]) == [1, 2, 3]

-- sortedKeyListUpdate
#guard B.sortedKeyListUpdate (B.sortedKeyListMk [1, 3, 5]) [2, 4] == [1, 2, 3, 4, 5]
#guard B.sortedKeyListUpdate (B.sortedKeyListMk ([] : List Nat)) [3, 1, 2] == [1, 2, 3]
#guard B.sortedKeyListUpdate (B.sortedKeyListMk [1, 2, 3]) ([] : List Nat) == [1, 2, 3]

-- ─────────── SortedSet ────────────────────────────────────────────────

-- sortedSetMk
#guard B.sortedSetMk ([] : List Nat) == ([] : List Nat)
#guard B.sortedSetMk [3, 1, 2] == [1, 2, 3]
#guard B.sortedSetMk [2, 2, 1, 3, 1] == [1, 2, 3]

-- sortedSetContains
#guard B.sortedSetContains (B.sortedSetMk [1, 2, 3]) 2 == true
#guard B.sortedSetContains (B.sortedSetMk [1, 2, 3]) 4 == false
#guard B.sortedSetContains (B.sortedSetMk ([] : List Nat)) 1 == false

-- sortedSetLen
#guard B.sortedSetLen (B.sortedSetMk ([] : List Nat)) == 0
#guard B.sortedSetLen (B.sortedSetMk [1, 2, 3]) == 3
#guard B.sortedSetLen (B.sortedSetMk [1, 1, 1]) == 1

-- sortedSetGetitem
#guard B.sortedSetGetitem (B.sortedSetMk [10, 20, 30]) 0 == 10
#guard B.sortedSetGetitem (B.sortedSetMk [10, 20, 30]) 2 == 30
#guard B.sortedSetGetitem (B.sortedSetMk ([] : List Nat)) 0 == (default : Nat)

-- sortedSetDelitem
#guard B.sortedSetDelitem (B.sortedSetMk [10, 20, 30]) 1 == [10, 30]
#guard B.sortedSetDelitem (B.sortedSetMk [10, 20, 30]) 0 == [20, 30]
#guard B.sortedSetDelitem (B.sortedSetMk [10, 20, 30]) 5 == [10, 20, 30]

-- sortedSetAdd
#guard B.sortedSetAdd (B.sortedSetMk ([] : List Nat)) 5 == [5]
#guard B.sortedSetAdd (B.sortedSetMk [1, 3, 5]) 2 == [1, 2, 3, 5]
#guard B.sortedSetAdd (B.sortedSetMk [1, 2, 3]) 2 == [1, 2, 3]

-- sortedSetDiscard
#guard B.sortedSetDiscard (B.sortedSetMk [1, 2, 3]) 2 == [1, 3]
#guard B.sortedSetDiscard (B.sortedSetMk [1, 2, 3]) 4 == [1, 2, 3]
#guard B.sortedSetDiscard (B.sortedSetMk [5]) 5 == ([] : List Nat)

-- sortedSetRemove
#guard B.sortedSetRemove (B.sortedSetMk [1, 2, 3]) 2 == [1, 3]
#guard B.sortedSetRemove (B.sortedSetMk [1, 2, 3]) 99 == [1, 2, 3]
#guard B.sortedSetRemove (B.sortedSetMk [5]) 5 == ([] : List Nat)

-- sortedSetCount
#guard B.sortedSetCount (B.sortedSetMk [1, 2, 3]) 2 == 1
#guard B.sortedSetCount (B.sortedSetMk [1, 2, 3]) 4 == 0
#guard B.sortedSetCount (B.sortedSetMk ([] : List Nat)) 0 == 0

-- sortedSetClear
#guard B.sortedSetClear (B.sortedSetMk [1, 2, 3]) == ([] : List Nat)
#guard B.sortedSetClear (B.sortedSetMk ([] : List Nat)) == ([] : List Nat)
#guard B.sortedSetClear (B.sortedSetMk [42]) == ([] : List Nat)

-- sortedSetCopy
#guard B.sortedSetCopy (B.sortedSetMk [1, 2, 3]) == [1, 2, 3]
#guard B.sortedSetCopy (B.sortedSetMk ([] : List Nat)) == ([] : List Nat)
#guard B.sortedSetCopy (B.sortedSetMk [3, 1, 2]) == [1, 2, 3]

-- sortedSetPop
#guard B.sortedSetPop (B.sortedSetMk [10, 20, 30]) 1 == 20
#guard B.sortedSetPop (B.sortedSetMk [10, 20, 30]) 0 == 10
#guard B.sortedSetPop (B.sortedSetMk ([] : List Nat)) 0 == (default : Nat)

-- sortedSetIter
#guard B.sortedSetIter (B.sortedSetMk [3, 1, 2]) == [1, 2, 3]
#guard B.sortedSetIter (B.sortedSetMk ([] : List Nat)) == ([] : List Nat)
#guard B.sortedSetIter (B.sortedSetMk [1, 1, 1]) == [1]

-- sortedSetReversed
#guard B.sortedSetReversed (B.sortedSetMk [1, 2, 3]) == [3, 2, 1]
#guard B.sortedSetReversed (B.sortedSetMk ([] : List Nat)) == ([] : List Nat)
#guard B.sortedSetReversed (B.sortedSetMk [42]) == [42]

-- sortedSetDifference
#guard B.sortedSetDifference (B.sortedSetMk [1, 2, 3, 4]) (B.sortedSetMk [2, 4]) == [1, 3]
#guard B.sortedSetDifference (B.sortedSetMk [1, 2, 3]) (B.sortedSetMk ([] : List Nat)) == [1, 2, 3]
#guard B.sortedSetDifference (B.sortedSetMk [1, 2]) (B.sortedSetMk [1, 2, 3]) == ([] : List Nat)

-- sortedSetDifferenceUpdate
#guard B.sortedSetDifferenceUpdate (B.sortedSetMk [1, 2, 3, 4]) (B.sortedSetMk [2, 4]) == [1, 3]
#guard B.sortedSetDifferenceUpdate (B.sortedSetMk [1, 2, 3]) (B.sortedSetMk ([] : List Nat)) == [1, 2, 3]
#guard B.sortedSetDifferenceUpdate (B.sortedSetMk [1, 2]) (B.sortedSetMk [1, 2, 3]) == ([] : List Nat)

-- sortedSetIntersection
#guard B.sortedSetIntersection (B.sortedSetMk [1, 2, 3, 4]) (B.sortedSetMk [2, 4, 6]) == [2, 4]
#guard B.sortedSetIntersection (B.sortedSetMk [1, 2, 3]) (B.sortedSetMk ([] : List Nat)) == ([] : List Nat)
#guard B.sortedSetIntersection (B.sortedSetMk [1, 2, 3]) (B.sortedSetMk [4, 5, 6]) == ([] : List Nat)

-- sortedSetIntersectionUpdate
#guard B.sortedSetIntersectionUpdate (B.sortedSetMk [1, 2, 3, 4]) (B.sortedSetMk [2, 4, 6]) == [2, 4]
#guard B.sortedSetIntersectionUpdate (B.sortedSetMk [1, 2, 3]) (B.sortedSetMk ([] : List Nat)) == ([] : List Nat)
#guard B.sortedSetIntersectionUpdate (B.sortedSetMk [1, 2, 3]) (B.sortedSetMk [4, 5, 6]) == ([] : List Nat)

-- sortedSetSymmetricDifference
#guard B.sortedSetSymmetricDifference (B.sortedSetMk [1, 2, 3, 4]) (B.sortedSetMk [3, 4, 5, 6]) == [1, 2, 5, 6]
#guard B.sortedSetSymmetricDifference (B.sortedSetMk [1, 2]) (B.sortedSetMk ([] : List Nat)) == [1, 2]
#guard B.sortedSetSymmetricDifference (B.sortedSetMk [1, 2]) (B.sortedSetMk [1, 2]) == ([] : List Nat)

-- sortedSetSymmetricDifferenceUpdate
#guard B.sortedSetSymmetricDifferenceUpdate (B.sortedSetMk [1, 2, 3, 4]) (B.sortedSetMk [3, 4, 5, 6]) == [1, 2, 5, 6]
#guard B.sortedSetSymmetricDifferenceUpdate (B.sortedSetMk [1, 2]) (B.sortedSetMk ([] : List Nat)) == [1, 2]
#guard B.sortedSetSymmetricDifferenceUpdate (B.sortedSetMk [1, 2]) (B.sortedSetMk [1, 2]) == ([] : List Nat)

-- sortedSetUnion
#guard B.sortedSetUnion (B.sortedSetMk [1, 2, 3]) (B.sortedSetMk [2, 4, 6]) == [1, 2, 3, 4, 6]
#guard B.sortedSetUnion (B.sortedSetMk ([] : List Nat)) (B.sortedSetMk [1, 2, 3]) == [1, 2, 3]
#guard B.sortedSetUnion (B.sortedSetMk [1, 2, 3]) (B.sortedSetMk [1, 2, 3]) == [1, 2, 3]

-- sortedSetUpdate
#guard B.sortedSetUpdate (B.sortedSetMk [1, 2, 3]) (B.sortedSetMk [2, 4, 6]) == [1, 2, 3, 4, 6]
#guard B.sortedSetUpdate (B.sortedSetMk ([] : List Nat)) (B.sortedSetMk [1, 2, 3]) == [1, 2, 3]
#guard B.sortedSetUpdate (B.sortedSetMk [1, 2, 3]) (B.sortedSetMk [1, 2, 3]) == [1, 2, 3]

-- ─────────── SortedDict ───────────────────────────────────────────────

-- sortedDictMk
#guard B.sortedDictMk ([] : List (Nat × Nat)) == ([] : List (Nat × Nat))
#guard B.sortedDictMk [(2, 20), (1, 10), (3, 30)] == [(1, 10), (2, 20), (3, 30)]
#guard B.sortedDictMk [(1, 10), (1, 99)] == [(1, 99)]

-- sortedDictDelitem
#guard B.sortedDictDelitem (B.sortedDictMk [(1, 10), (2, 20)]) 1 == [(2, 20)]
#guard B.sortedDictDelitem (B.sortedDictMk [(1, 10), (2, 20)]) 99 == [(1, 10), (2, 20)]
#guard B.sortedDictDelitem (B.sortedDictMk ([] : List (Nat × Nat))) 1 == ([] : List (Nat × Nat))

-- sortedDictSetitem
#guard B.sortedDictSetitem (B.sortedDictMk [(1, 10)]) 2 20 == [(1, 10), (2, 20)]
#guard B.sortedDictSetitem (B.sortedDictMk [(1, 10), (2, 20)]) 1 99 == [(1, 99), (2, 20)]
#guard B.sortedDictSetitem (B.sortedDictMk ([] : List (Nat × Nat))) 5 50 == [(5, 50)]

-- sortedDictIter
#guard B.sortedDictIter (B.sortedDictMk [(1, 10), (2, 20), (3, 30)]) == [1, 2, 3]
#guard B.sortedDictIter (B.sortedDictMk ([] : List (Nat × Nat))) == ([] : List Nat)
#guard B.sortedDictIter (B.sortedDictMk [(2, 20), (1, 10)]) == [1, 2]

-- sortedDictReversed
#guard B.sortedDictReversed (B.sortedDictMk [(1, 10), (2, 20), (3, 30)]) == [3, 2, 1]
#guard B.sortedDictReversed (B.sortedDictMk ([] : List (Nat × Nat))) == ([] : List Nat)
#guard B.sortedDictReversed (B.sortedDictMk [(2, 20), (1, 10)]) == [2, 1]

-- sortedDictClear
#guard B.sortedDictClear (B.sortedDictMk [(1, 10), (2, 20)]) == ([] : List (Nat × Nat))
#guard B.sortedDictClear (B.sortedDictMk ([] : List (Nat × Nat))) == ([] : List (Nat × Nat))
#guard B.sortedDictClear (B.sortedDictMk [(42, 99)]) == ([] : List (Nat × Nat))

-- sortedDictCopy
#guard B.sortedDictCopy (B.sortedDictMk [(1, 10), (2, 20)]) == [(1, 10), (2, 20)]
#guard B.sortedDictCopy (B.sortedDictMk ([] : List (Nat × Nat))) == ([] : List (Nat × Nat))
#guard B.sortedDictCopy (B.sortedDictMk [(2, 20), (1, 10)]) == [(1, 10), (2, 20)]

-- sortedDictItems
#guard B.sortedDictItems (B.sortedDictMk [(1, 10), (2, 20)]) == [(1, 10), (2, 20)]
#guard B.sortedDictItems (B.sortedDictMk ([] : List (Nat × Nat))) == ([] : List (Nat × Nat))
#guard B.sortedDictItems (B.sortedDictMk [(2, 20), (1, 10), (3, 30)]) == [(1, 10), (2, 20), (3, 30)]

-- sortedDictKeys
#guard B.sortedDictKeys (B.sortedDictMk [(1, 10), (2, 20), (3, 30)]) == [1, 2, 3]
#guard B.sortedDictKeys (B.sortedDictMk ([] : List (Nat × Nat))) == ([] : List Nat)
#guard B.sortedDictKeys (B.sortedDictMk [(3, 30), (1, 10), (2, 20)]) == [1, 2, 3]

-- sortedDictValues
#guard B.sortedDictValues (B.sortedDictMk [(1, 10), (2, 20), (3, 30)]) == [10, 20, 30]
#guard B.sortedDictValues (B.sortedDictMk ([] : List (Nat × Nat))) == ([] : List Nat)
#guard B.sortedDictValues (B.sortedDictMk [(3, 30), (1, 10), (2, 20)]) == [10, 20, 30]

-- sortedDictPop
#guard B.sortedDictPop (B.sortedDictMk [(1, 10), (2, 20), (3, 30)]) 2 0 == 20
#guard B.sortedDictPop (B.sortedDictMk [(1, 10)]) 5 99 == 99
#guard B.sortedDictPop (B.sortedDictMk ([] : List (Nat × Nat))) 1 42 == 42

-- sortedDictPopitem
#guard B.sortedDictPopitem (B.sortedDictMk [(1, 10), (2, 20), (3, 30)]) 1 == (2, 20)
#guard B.sortedDictPopitem (B.sortedDictMk [(1, 10), (2, 20), (3, 30)]) 0 == (1, 10)
#guard B.sortedDictPopitem (B.sortedDictMk ([] : List (Nat × Nat))) 0 == ((default, default) : Nat × Nat)

-- sortedDictPeekitem
#guard B.sortedDictPeekitem (B.sortedDictMk [(1, 10), (2, 20), (3, 30)]) 1 == (2, 20)
#guard B.sortedDictPeekitem (B.sortedDictMk [(1, 10), (2, 20), (3, 30)]) 0 == (1, 10)
#guard B.sortedDictPeekitem (B.sortedDictMk ([] : List (Nat × Nat))) 0 == ((default, default) : Nat × Nat)

-- sortedDictSetdefault
#guard B.sortedDictSetdefault (B.sortedDictMk [(1, 10)]) 1 99 == [(1, 10)]
#guard B.sortedDictSetdefault (B.sortedDictMk [(1, 10)]) 2 20 == [(1, 10), (2, 20)]
#guard B.sortedDictSetdefault (B.sortedDictMk ([] : List (Nat × Nat))) 5 50 == [(5, 50)]
