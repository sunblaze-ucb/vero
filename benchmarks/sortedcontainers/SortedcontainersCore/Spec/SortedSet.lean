import SortedcontainersCore.Spec.Aux

/-!
# SortedcontainersCore.Spec.SortedSet

Structural specifications for `SortedSet` APIs.
Each `spec_*` is a property over an arbitrary `impl : RepoImpl`.
-/

/-- Constructing a `SortedSet` exposes sorted iteration and rebuilding from that view is
idempotent. -/
def spec_sortedSet_mk_sorted_idempotent (impl : RepoImpl) : Prop :=
  ∀ xs : List Nat,
    let s := impl.sortedcontainersCore.sortedSetMk (α := Nat) xs
    spec_helper_sortedByOrd (impl.sortedcontainersCore.sortedSetIter s) ∧
    impl.sortedcontainersCore.sortedSetMk
      (impl.sortedcontainersCore.sortedSetIter s) = s

/-- Adding an element to a sorted set makes it present, preserves sorted iteration, and is
idempotent for that element. -/
def spec_sortedSet_add_membership_idempotent (impl : RepoImpl) : Prop :=
  ∀ (s : SortedContainers.SortedSet Nat) (x : Nat),
    spec_helper_sortedByOrd (impl.sortedcontainersCore.sortedSetIter s) →
      impl.sortedcontainersCore.sortedSetContains
        (impl.sortedcontainersCore.sortedSetAdd s x) x = true ∧
      spec_helper_sortedByOrd
        (impl.sortedcontainersCore.sortedSetIter
          (impl.sortedcontainersCore.sortedSetAdd s x)) ∧
      impl.sortedcontainersCore.sortedSetAdd
        (impl.sortedcontainersCore.sortedSetAdd s x) x =
        impl.sortedcontainersCore.sortedSetAdd s x

/-- `count` is exactly the numeric view of `contains`, so set membership is zero-or-one. -/
def spec_sortedSet_count_contains_law (impl : RepoImpl) : Prop :=
  ∀ (s : SortedContainers.SortedSet Nat) (x : Nat),
    impl.sortedcontainersCore.sortedSetCount s x =
      if impl.sortedcontainersCore.sortedSetContains s x then 1 else 0

/-- Union contains both inputs, while intersection is contained in both inputs. -/
def spec_sortedSet_union_intersection_subset_laws (impl : RepoImpl) : Prop :=
  ∀ a b : SortedContainers.SortedSet Nat,
    spec_helper_containsAll
      (impl.sortedcontainersCore.sortedSetIter a)
      (impl.sortedcontainersCore.sortedSetIter
        (impl.sortedcontainersCore.sortedSetUnion a b)) ∧
    spec_helper_containsAll
      (impl.sortedcontainersCore.sortedSetIter b)
      (impl.sortedcontainersCore.sortedSetIter
        (impl.sortedcontainersCore.sortedSetUnion a b)) ∧
    spec_helper_containsAll
      (impl.sortedcontainersCore.sortedSetIter
        (impl.sortedcontainersCore.sortedSetIntersection a b))
      (impl.sortedcontainersCore.sortedSetIter a) ∧
    spec_helper_containsAll
      (impl.sortedcontainersCore.sortedSetIter
      (impl.sortedcontainersCore.sortedSetIntersection a b))
      (impl.sortedcontainersCore.sortedSetIter b)

/-- Union contains exactly the elements present in either input set. -/
def spec_sortedSet_union_exact_membership (impl : RepoImpl) : Prop :=
  ∀ (a b : SortedContainers.SortedSet Nat) (x : Nat),
    x ∈ impl.sortedcontainersCore.sortedSetIter
      (impl.sortedcontainersCore.sortedSetUnion a b) ↔
    x ∈ impl.sortedcontainersCore.sortedSetIter a ∨
      x ∈ impl.sortedcontainersCore.sortedSetIter b

/-- Intersection contains exactly the elements present in both input sets.
Requires both inputs to be well-formed (sorted) sets: the binary-search `contains`
underlying `intersection` is only correct on sorted lists. -/
def spec_sortedSet_intersection_exact_membership (impl : RepoImpl) : Prop :=
  ∀ (a b : SortedContainers.SortedSet Nat) (x : Nat),
    spec_helper_sortedByOrd (impl.sortedcontainersCore.sortedSetIter a) →
    spec_helper_sortedByOrd (impl.sortedcontainersCore.sortedSetIter b) →
    (x ∈ impl.sortedcontainersCore.sortedSetIter
      (impl.sortedcontainersCore.sortedSetIntersection a b) ↔
    x ∈ impl.sortedcontainersCore.sortedSetIter a ∧
      x ∈ impl.sortedcontainersCore.sortedSetIter b)

/-- The update-style set APIs are observationally equal to their pure counterparts. -/
def spec_sortedSet_update_variants_match_pure_ops (impl : RepoImpl) : Prop :=
  ∀ a b : SortedContainers.SortedSet Nat,
    impl.sortedcontainersCore.sortedSetDifferenceUpdate a b =
      impl.sortedcontainersCore.sortedSetDifference a b ∧
    impl.sortedcontainersCore.sortedSetIntersectionUpdate a b =
      impl.sortedcontainersCore.sortedSetIntersection a b ∧
    impl.sortedcontainersCore.sortedSetSymmetricDifferenceUpdate a b =
      impl.sortedcontainersCore.sortedSetSymmetricDifference a b ∧
    impl.sortedcontainersCore.sortedSetUpdate a b =
      impl.sortedcontainersCore.sortedSetUnion a b

/-- The standard self-laws hold for well-formed sets built by `mk`. -/
def spec_sortedSet_algebraic_self_laws (impl : RepoImpl) : Prop :=
  ∀ xs : List Nat,
    let s := impl.sortedcontainersCore.sortedSetMk (α := Nat) xs
    impl.sortedcontainersCore.sortedSetUnion s s = s ∧
    impl.sortedcontainersCore.sortedSetIntersection s s = s ∧
    impl.sortedcontainersCore.sortedSetDifference s s = [] ∧
    impl.sortedcontainersCore.sortedSetSymmetricDifference s s = []

-- ── Restored from backup (T1B over-trim recovery) ──────────────────────

/-- Adding a value already present in the set is a no-op — the set is unchanged. -/
def spec_sortedSet_add_dedup_noop (impl : RepoImpl) : Prop :=
  let s : List Nat := [1, 2, 3]
  impl.sortedcontainersCore.sortedSetAdd s 2 = s ∧
  impl.sortedcontainersCore.sortedSetContains
    (impl.sortedcontainersCore.sortedSetAdd s 2) 2 = true

/-- Adding a new (absent) value to a set makes `contains` return `true` for it. -/
def spec_sortedSet_add_new_then_contains (impl : RepoImpl) : Prop :=
  let s : List Nat := [1, 3, 5]
  impl.sortedcontainersCore.sortedSetContains
    (impl.sortedcontainersCore.sortedSetAdd s 2) 2 = true ∧
  impl.sortedcontainersCore.sortedSetContains
    (impl.sortedcontainersCore.sortedSetAdd ([] : List Nat) 7) 7 = true

/-- `clear` returns the empty set. -/
def spec_sortedSet_clear_is_nil (impl : RepoImpl) : Prop :=
  impl.sortedcontainersCore.sortedSetClear (α := Nat) [1, 2, 3] = [] ∧
  impl.sortedcontainersCore.sortedSetClear (α := Nat) [] = []

/-- After building a set, `contains` is true for all original elements and false for absent
ones. -/
def spec_sortedSet_contains_after_mk (impl : RepoImpl) : Prop :=
  let s := impl.sortedcontainersCore.sortedSetMk (α := Nat) [3, 1, 2]
  impl.sortedcontainersCore.sortedSetContains s 2 = true ∧
  impl.sortedcontainersCore.sortedSetContains s 5 = false

/-- `copy` is the identity. -/
def spec_sortedSet_copy_is_id (impl : RepoImpl) : Prop :=
  let s : List Nat := [1, 2, 3]
  impl.sortedcontainersCore.sortedSetCopy s = s ∧
  impl.sortedcontainersCore.sortedSetCopy ([] : List Nat) = []

/-- `delitem i s` removes the element at position `i` from the set. -/
def spec_sortedSet_delitem_concrete (impl : RepoImpl) : Prop :=
  let s := impl.sortedcontainersCore.sortedSetMk (α := Nat) [1, 2, 3]
  impl.sortedcontainersCore.sortedSetDelitem s 1 = [1, 3] ∧
  impl.sortedcontainersCore.sortedSetDelitem s 5 = [1, 2, 3]

/-- `difference s1 s2` returns elements in `s1` not in `s2`, maintaining sorted order. -/
def spec_sortedSet_difference_concrete (impl : RepoImpl) : Prop :=
  let s1 := impl.sortedcontainersCore.sortedSetMk (α := Nat) [1, 2, 3, 4]
  let s2 := impl.sortedcontainersCore.sortedSetMk (α := Nat) [2, 4]
  impl.sortedcontainersCore.sortedSetDifference s1 s2 = [1, 3] ∧
  impl.sortedcontainersCore.sortedSetDifference s1 ([] : List Nat) = s1

/-- `discard s v` removes `v` if present; absent value is a no-op. -/
def spec_sortedSet_discard_concrete (impl : RepoImpl) : Prop :=
  let s : List Nat := [1, 2, 3, 4]
  impl.sortedcontainersCore.sortedSetDiscard s 3 = [1, 2, 4] ∧
  impl.sortedcontainersCore.sortedSetDiscard s 9 = [1, 2, 3, 4]

/-- `getitem i s` returns the `i`-th unique sorted element; OOB returns `default`. -/
def spec_sortedSet_getitem_concrete (impl : RepoImpl) : Prop :=
  let s := impl.sortedcontainersCore.sortedSetMk (α := Nat) [3, 1, 2]
  impl.sortedcontainersCore.sortedSetGetitem s 0 = 1 ∧
  impl.sortedcontainersCore.sortedSetGetitem s 2 = 3 ∧
  impl.sortedcontainersCore.sortedSetGetitem s 9 = 0

/-- `intersection s1 s2` returns elements present in both sets. -/
def spec_sortedSet_intersection_concrete (impl : RepoImpl) : Prop :=
  let s1 := impl.sortedcontainersCore.sortedSetMk (α := Nat) [1, 2, 3, 4]
  let s2 := impl.sortedcontainersCore.sortedSetMk (α := Nat) [2, 4, 5]
  impl.sortedcontainersCore.sortedSetIntersection s1 s2 = [2, 4] ∧
  impl.sortedcontainersCore.sortedSetIntersection s1 ([] : List Nat) = []

/-- `iter s = s` — iterating yields the underlying sorted list. -/
def spec_sortedSet_iter_eq_underlying (impl : RepoImpl) : Prop :=
  let s := impl.sortedcontainersCore.sortedSetMk (α := Nat) [3, 1, 2, 3]
  impl.sortedcontainersCore.sortedSetIter s = s ∧
  impl.sortedcontainersCore.sortedSetIter ([] : List Nat) = []

/-- `len` returns the number of unique elements after deduplication. -/
def spec_sortedSet_len_concrete (impl : RepoImpl) : Prop :=
  impl.sortedcontainersCore.sortedSetLen
    (impl.sortedcontainersCore.sortedSetMk (α := Nat) [3, 1, 2, 1]) = 3 ∧
  impl.sortedcontainersCore.sortedSetLen
    (impl.sortedcontainersCore.sortedSetMk (α := Nat) []) = 0

/-- `SortedSet.mk` sorts its input and removes duplicates, producing a strictly ascending list of
unique elements. -/
def spec_sortedSet_mk_dedup_sort (impl : RepoImpl) : Prop :=
  impl.sortedcontainersCore.sortedSetMk (α := Nat) [3, 1, 2, 1, 3] = [1, 2, 3] ∧
  impl.sortedcontainersCore.sortedSetMk (α := Nat) [] = [] ∧
  impl.sortedcontainersCore.sortedSetMk (α := Nat) [5, 5, 5] = [5]

/-- `pop i s = getitem i s` — in the pure model both return the `i`-th element. -/
def spec_sortedSet_pop_eq_getitem (impl : RepoImpl) : Prop :=
  let s : List Nat := [1, 2, 3, 4]
  impl.sortedcontainersCore.sortedSetPop s 2 =
  impl.sortedcontainersCore.sortedSetGetitem s 2 ∧
  impl.sortedcontainersCore.sortedSetPop s 9 =
  impl.sortedcontainersCore.sortedSetGetitem s 9

/-- On present values, `remove` and `discard` remove the same value for `SortedSet`.
Absent-value Python error behavior is not representable in this pure Lean signature. -/
def spec_sortedSet_remove_eq_discard (impl : RepoImpl) : Prop :=
  ∀ (s : SortedContainers.SortedSet Nat) (x : Nat),
    impl.sortedcontainersCore.sortedSetContains s x = true →
      impl.sortedcontainersCore.sortedSetRemove s x =
        impl.sortedcontainersCore.sortedSetDiscard s x

/-- `reversed s = (iter s).reverse`. -/
def spec_sortedSet_reversed_eq_iterRev (impl : RepoImpl) : Prop :=
  let s : List Nat := [1, 2, 3, 4]
  impl.sortedcontainersCore.sortedSetReversed s =
  (impl.sortedcontainersCore.sortedSetIter s).reverse

/-- `symmetric_difference s1 s2` returns elements in exactly one of the sets. -/
def spec_sortedSet_symmetricDifference_concrete (impl : RepoImpl) : Prop :=
  let s1 := impl.sortedcontainersCore.sortedSetMk (α := Nat) [1, 2, 3]
  let s2 := impl.sortedcontainersCore.sortedSetMk (α := Nat) [2, 3, 4]
  impl.sortedcontainersCore.sortedSetSymmetricDifference s1 s2 = [1, 4] ∧
  impl.sortedcontainersCore.sortedSetSymmetricDifference s1 ([] : List Nat) = s1

/-- `union s1 s2` is the sorted set of all elements from either set. -/
def spec_sortedSet_union_concrete (impl : RepoImpl) : Prop :=
  let s1 := impl.sortedcontainersCore.sortedSetMk (α := Nat) [1, 3, 5]
  let s2 := impl.sortedcontainersCore.sortedSetMk (α := Nat) [2, 3, 4]
  impl.sortedcontainersCore.sortedSetUnion s1 s2 = [1, 2, 3, 4, 5] ∧
  impl.sortedcontainersCore.sortedSetUnion s1 ([] : List Nat) = s1

-- ── Manual PR-35 ports (stand-alone) ───────────────────────────────────

/-- PR-35 Spec 7 (manual): the union of two sorted sets contains every element from each input. -/
def spec_sortedSet_union_contains_inputs (impl : RepoImpl) : Prop :=
  ∀ a b : SortedContainers.SortedSet Nat,
    spec_helper_containsAll
      (impl.sortedcontainersCore.sortedSetIter a)
      (impl.sortedcontainersCore.sortedSetIter
        (impl.sortedcontainersCore.sortedSetUnion a b)) ∧
    spec_helper_containsAll
      (impl.sortedcontainersCore.sortedSetIter b)
      (impl.sortedcontainersCore.sortedSetIter
        (impl.sortedcontainersCore.sortedSetUnion a b))

/-- PR-35 Spec 8 (manual): the intersection of two sorted sets is contained in both inputs. -/
def spec_sortedSet_intersection_contained (impl : RepoImpl) : Prop :=
  ∀ a b : SortedContainers.SortedSet Nat,
    spec_helper_containsAll
      (impl.sortedcontainersCore.sortedSetIter
        (impl.sortedcontainersCore.sortedSetIntersection a b))
      (impl.sortedcontainersCore.sortedSetIter a) ∧
    spec_helper_containsAll
      (impl.sortedcontainersCore.sortedSetIter
        (impl.sortedcontainersCore.sortedSetIntersection a b))
      (impl.sortedcontainersCore.sortedSetIter b)
