import SortedcontainersCore.Bundle

/-!
# SortedcontainersCore.Harness

Benchmark harness: `RepoImpl` structure (one field per package),
`canonical` instance wiring, and the `joint_unsat` macro consumed by
`codeproof`-mode `Proof/Joint.lean`.

DO NOT MODIFY this file. This is the benchmark infrastructure.
-/

-- ── Implementation bundle (one field per package) ───────────────────────

structure RepoImpl where
  sortedcontainersCore : SortedcontainersCoreBundle

-- ── Canonical instance ───────────────────────────────────────────────────

def canonical : RepoImpl where
  sortedcontainersCore := {
    -- SortedList
    sortedListMk          := SortedContainers.SortedList.mk
    sortedListContains    := SortedContainers.SortedList.contains
    sortedListLen         := SortedContainers.SortedList.len
    sortedListGetitem     := SortedContainers.SortedList.getitem
    sortedListDelitem     := SortedContainers.SortedList.delitem
    sortedListAdd         := SortedContainers.SortedList.add
    sortedListDiscard     := SortedContainers.SortedList.discard
    sortedListRemove      := SortedContainers.SortedList.remove
    sortedListUpdate      := SortedContainers.SortedList.update
    sortedListExtend      := SortedContainers.SortedList.extend
    sortedListBisectLeft  := SortedContainers.SortedList.bisect_left
    sortedListBisectRight := SortedContainers.SortedList.bisect_right
    sortedListCount       := SortedContainers.SortedList.count
    sortedListIndex       := SortedContainers.SortedList.index
    sortedListClear       := SortedContainers.SortedList.clear
    sortedListCopy        := SortedContainers.SortedList.copy
    sortedListPop         := SortedContainers.SortedList.pop
    sortedListIrange      := SortedContainers.SortedList.irange
    sortedListIslice      := SortedContainers.SortedList.islice
    sortedListIter        := SortedContainers.SortedList.iter
    sortedListReversed    := SortedContainers.SortedList.reversed
    -- SortedKeyList
    sortedKeyListMk           := SortedContainers.SortedKeyList.mk
    sortedKeyListContains     := SortedContainers.SortedKeyList.contains
    sortedKeyListAdd          := SortedContainers.SortedKeyList.add
    sortedKeyListDiscard      := SortedContainers.SortedKeyList.discard
    sortedKeyListRemove       := SortedContainers.SortedKeyList.remove
    sortedKeyListBisectLeft   := SortedContainers.SortedKeyList.bisect_left
    sortedKeyListBisectRight  := SortedContainers.SortedKeyList.bisect_right
    sortedKeyListCount        := SortedContainers.SortedKeyList.count
    sortedKeyListIndex        := SortedContainers.SortedKeyList.index
    sortedKeyListIrange       := SortedContainers.SortedKeyList.irange
    sortedKeyListIrangeKey    := SortedContainers.SortedKeyList.irange_key
    sortedKeyListClear        := SortedContainers.SortedKeyList.clear
    sortedKeyListCopy         := SortedContainers.SortedKeyList.copy
    sortedKeyListUpdate       := SortedContainers.SortedKeyList.update
    -- SortedSet
    sortedSetMk                        := SortedContainers.SortedSet.mk
    sortedSetContains                  := SortedContainers.SortedSet.contains
    sortedSetLen                       := SortedContainers.SortedSet.len
    sortedSetGetitem                   := SortedContainers.SortedSet.getitem
    sortedSetDelitem                   := SortedContainers.SortedSet.delitem
    sortedSetAdd                       := SortedContainers.SortedSet.add
    sortedSetDiscard                   := SortedContainers.SortedSet.discard
    sortedSetRemove                    := SortedContainers.SortedSet.remove
    sortedSetCount                     := SortedContainers.SortedSet.count
    sortedSetClear                     := SortedContainers.SortedSet.clear
    sortedSetCopy                      := SortedContainers.SortedSet.copy
    sortedSetPop                       := SortedContainers.SortedSet.pop
    sortedSetIter                      := SortedContainers.SortedSet.iter
    sortedSetReversed                  := SortedContainers.SortedSet.reversed
    sortedSetDifference                := SortedContainers.SortedSet.difference
    sortedSetDifferenceUpdate          := SortedContainers.SortedSet.difference_update
    sortedSetIntersection              := SortedContainers.SortedSet.intersection
    sortedSetIntersectionUpdate        := SortedContainers.SortedSet.intersection_update
    sortedSetSymmetricDifference       := SortedContainers.SortedSet.symmetric_difference
    sortedSetSymmetricDifferenceUpdate := SortedContainers.SortedSet.symmetric_difference_update
    sortedSetUnion                     := SortedContainers.SortedSet.union
    sortedSetUpdate                    := SortedContainers.SortedSet.update
    -- SortedDict
    sortedDictMk         := SortedContainers.SortedDict.mk
    sortedDictDelitem    := SortedContainers.SortedDict.delitem
    sortedDictSetitem    := SortedContainers.SortedDict.setitem
    sortedDictIter       := SortedContainers.SortedDict.iter
    sortedDictReversed   := SortedContainers.SortedDict.reversed
    sortedDictClear      := SortedContainers.SortedDict.clear
    sortedDictCopy       := SortedContainers.SortedDict.copy
    sortedDictItems      := SortedContainers.SortedDict.items
    sortedDictKeys       := SortedContainers.SortedDict.keys
    sortedDictValues     := SortedContainers.SortedDict.values
    sortedDictPop        := SortedContainers.SortedDict.pop
    sortedDictPopitem    := SortedContainers.SortedDict.popitem
    sortedDictPeekitem   := SortedContainers.SortedDict.peekitem
    sortedDictSetdefault := SortedContainers.SortedDict.setdefault
  }

-- ── joint_unsat macro ────────────────────────────────────────────────────

/--
`joint_unsat spec_A spec_B [spec_C …] by <proof>` generates
```
theorem joint_unsat.spec_A.spec_B.… :
    ¬ ∃ impl : RepoImpl, spec_A impl ∧ spec_B impl ∧ … := by <proof>
```

Specs appear in the caller's order. No sorting, no deduplication —
anti-cheat for joint-unsat claims is enforced at evaluation by
extracting the spec list from the companion `!solution` marker
(rejecting duplicates there) and rerendering this macro from the
extracted list.
-/
syntax "joint_unsat" ident ident ident* "by" tacticSeq : command

open Lean in
macro_rules
  | `(joint_unsat $s1 $s2 $[$rest]* by $proof) => do
    let specs := #[s1, s2] ++ rest
    let name := specs.foldl (init := `joint_unsat) fun acc s => Name.append acc s.getId
    let mut body ← `($(specs[0]!) impl)
    for s in specs[1:] do
      body ← `($body ∧ $s impl)
    `(theorem $(mkIdent name) : ¬ ∃ impl : RepoImpl, $body := by $proof)
