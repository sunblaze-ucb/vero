import SortedcontainersCore.Spec.Aux

/-!
# SortedcontainersCore.Spec.SortedList

Structural specifications for `SortedList` and `SortedKeyList` APIs.
Each `spec_*` is a property over an arbitrary `impl : RepoImpl`.
-/

/-- Constructing a `SortedList` exposes a sorted iterator for every input list. -/
def spec_sortedList_mk_iter_sorted (impl : RepoImpl) : Prop :=
  ∀ xs : List Nat,
    spec_helper_sortedByOrd
      (impl.sortedcontainersCore.sortedListIter
        (impl.sortedcontainersCore.sortedListMk (α := Nat) xs))

/-- Constructing a `SortedList` preserves the multiplicity of every input element. -/
def spec_sortedList_mk_preserves_multiset (impl : RepoImpl) : Prop :=
  ∀ (xs : List Nat) (x : Nat),
    spec_helper_countNat x
      (impl.sortedcontainersCore.sortedListIter
        (impl.sortedcontainersCore.sortedListMk (α := Nat) xs)) =
    spec_helper_countNat x xs

/-- Adding to a sorted `SortedList` preserves sorted iteration, increases length by one, and
makes the inserted value observable through `contains`. -/
def spec_sortedList_add_preserves_shape (impl : RepoImpl) : Prop :=
  ∀ (s : SortedContainers.SortedList Nat) (x : Nat),
    spec_helper_sortedByOrd (impl.sortedcontainersCore.sortedListIter s) →
      spec_helper_sortedByOrd
        (impl.sortedcontainersCore.sortedListIter
          (impl.sortedcontainersCore.sortedListAdd s x)) ∧
      impl.sortedcontainersCore.sortedListLen
        (impl.sortedcontainersCore.sortedListAdd s x) =
        impl.sortedcontainersCore.sortedListLen s + 1 ∧
      impl.sortedcontainersCore.sortedListContains
        (impl.sortedcontainersCore.sortedListAdd s x) x = true

/-- Adding to a `SortedList` preserves old multiplicities and adds exactly one copy of `x`. -/
def spec_sortedList_add_count_law (impl : RepoImpl) : Prop :=
  ∀ (s : SortedContainers.SortedList Nat) (x y : Nat),
    spec_helper_sortedByOrd (impl.sortedcontainersCore.sortedListIter s) →
      spec_helper_countNat y
        (impl.sortedcontainersCore.sortedListIter
          (impl.sortedcontainersCore.sortedListAdd s x)) =
      spec_helper_countNat y (impl.sortedcontainersCore.sortedListIter s) +
        if y == x then 1 else 0

/-- Discarding from a sorted `SortedList` preserves sorted iteration and cannot increase length. -/
def spec_sortedList_discard_preserves_order_and_bounds (impl : RepoImpl) : Prop :=
  ∀ (s : SortedContainers.SortedList Nat) (x : Nat),
    spec_helper_sortedByOrd (impl.sortedcontainersCore.sortedListIter s) →
      spec_helper_sortedByOrd
        (impl.sortedcontainersCore.sortedListIter
          (impl.sortedcontainersCore.sortedListDiscard s x)) ∧
      impl.sortedcontainersCore.sortedListLen
        (impl.sortedcontainersCore.sortedListDiscard s x) ≤
        impl.sortedcontainersCore.sortedListLen s

/-- The bisect operations bracket all occurrences: left ≤ right ≤ length, and count is the gap. -/
def spec_sortedList_bisect_count_law (impl : RepoImpl) : Prop :=
  ∀ (s : SortedContainers.SortedList Nat) (x : Nat),
    impl.sortedcontainersCore.sortedListBisectLeft s x ≤
      impl.sortedcontainersCore.sortedListBisectRight s x ∧
    impl.sortedcontainersCore.sortedListBisectRight s x ≤
      impl.sortedcontainersCore.sortedListLen s ∧
      impl.sortedcontainersCore.sortedListCount s x =
      impl.sortedcontainersCore.sortedListBisectRight s x -
      impl.sortedcontainersCore.sortedListBisectLeft s x

/-- `bisect_left` is the first index whose value is not less than `x`. -/
def spec_sortedList_bisectLeft_exact (impl : RepoImpl) : Prop :=
  ∀ (s : SortedContainers.SortedList Nat) (x i y : Nat),
    spec_helper_sortedByOrd (impl.sortedcontainersCore.sortedListIter s) →
      let left := impl.sortedcontainersCore.sortedListBisectLeft s x
      (impl.sortedcontainersCore.sortedListIter s)[i]? = some y →
        (i < left → y < x) ∧ (left ≤ i → x ≤ y)

/-- `bisect_right` is the first index whose value is greater than `x`. -/
def spec_sortedList_bisectRight_exact (impl : RepoImpl) : Prop :=
  ∀ (s : SortedContainers.SortedList Nat) (x i y : Nat),
    spec_helper_sortedByOrd (impl.sortedcontainersCore.sortedListIter s) →
      let right := impl.sortedcontainersCore.sortedListBisectRight s x
      (impl.sortedcontainersCore.sortedListIter s)[i]? = some y →
        (i < right → y ≤ x) ∧ (right ≤ i → x < y)

/-- `update` and `extend` are the same bulk-insert operation, and their output iterates sorted. -/
def spec_sortedList_update_extend_law (impl : RepoImpl) : Prop :=
  ∀ (s xs : List Nat),
    spec_helper_sortedByOrd (impl.sortedcontainersCore.sortedListIter s) →
      impl.sortedcontainersCore.sortedListUpdate s xs =
        impl.sortedcontainersCore.sortedListExtend s xs ∧
      spec_helper_sortedByOrd
        (impl.sortedcontainersCore.sortedListIter
          (impl.sortedcontainersCore.sortedListUpdate s xs))

/-- In this model `SortedKeyList` shares the core observable behavior of `SortedList` and
`irange_key` delegates to `irange`. -/
def spec_sortedKeyList_matches_sortedList_core (impl : RepoImpl) : Prop :=
  ∀ (xs : List Nat) (x lo hi : Nat) (inclusive reverse : Bool),
    impl.sortedcontainersCore.sortedKeyListMk (α := Nat) xs =
      impl.sortedcontainersCore.sortedListMk (α := Nat) xs ∧
    impl.sortedcontainersCore.sortedKeyListContains
      (impl.sortedcontainersCore.sortedKeyListMk (α := Nat) xs) x =
      impl.sortedcontainersCore.sortedListContains
        (impl.sortedcontainersCore.sortedListMk (α := Nat) xs) x ∧
    impl.sortedcontainersCore.sortedKeyListBisectLeft
      (impl.sortedcontainersCore.sortedKeyListMk (α := Nat) xs) x =
      impl.sortedcontainersCore.sortedListBisectLeft
        (impl.sortedcontainersCore.sortedListMk (α := Nat) xs) x ∧
    impl.sortedcontainersCore.sortedKeyListBisectRight
      (impl.sortedcontainersCore.sortedKeyListMk (α := Nat) xs) x =
      impl.sortedcontainersCore.sortedListBisectRight
        (impl.sortedcontainersCore.sortedListMk (α := Nat) xs) x ∧
    impl.sortedcontainersCore.sortedKeyListIrangeKey
      (impl.sortedcontainersCore.sortedKeyListMk (α := Nat) xs) lo hi inclusive reverse =
      impl.sortedcontainersCore.sortedKeyListIrange
        (impl.sortedcontainersCore.sortedKeyListMk (α := Nat) xs) lo hi inclusive reverse

-- ── Restored from backup (T1B over-trim recovery) ──────────────────────

/-- True iff `xs` is non-strictly sorted in ascending order (each adjacent pair satisfies a ≤ b). -/
def spec_helper_isSorted (xs : List Nat) : Bool :=
  (xs.zip xs.tail).all (fun p => decide (p.1 ≤ p.2))

/-- True iff `xs` is strictly sorted in ascending order (each adjacent pair satisfies a < b). -/
def spec_helper_isStrictSorted (xs : List Nat) : Bool :=
  (xs.zip xs.tail).all (fun p => decide (p.1 < p.2))

/-- After adding a value to a `SortedKeyList`, `contains` returns `true` for that value. -/
def spec_sortedKeyList_add_then_contains (impl : RepoImpl) : Prop :=
  let s : List Nat := [1, 3, 5]
  impl.sortedcontainersCore.sortedKeyListContains
    (impl.sortedcontainersCore.sortedKeyListAdd s 2) 2 = true

/-- `sortedKeyListBisectLeft s v` is the leftmost insertion point for `v`. -/
def spec_sortedKeyList_bisectLeft_concrete (impl : RepoImpl) : Prop :=
  let s := impl.sortedcontainersCore.sortedKeyListMk (α := Nat) [1, 2, 2, 4]
  impl.sortedcontainersCore.sortedKeyListBisectLeft s 2 = 1 ∧
  impl.sortedcontainersCore.sortedKeyListBisectLeft s 3 = 3 ∧
  impl.sortedcontainersCore.sortedKeyListBisectLeft s 0 = 0

/-- `sortedKeyListBisectRight s v` is the rightmost insertion point for `v`. -/
def spec_sortedKeyList_bisectRight_concrete (impl : RepoImpl) : Prop :=
  let s := impl.sortedcontainersCore.sortedKeyListMk (α := Nat) [1, 2, 2, 4]
  impl.sortedcontainersCore.sortedKeyListBisectRight s 2 = 3 ∧
  impl.sortedcontainersCore.sortedKeyListBisectRight s 3 = 3 ∧
  impl.sortedcontainersCore.sortedKeyListBisectRight s 5 = 4

/-- `clear` returns the empty list. -/
def spec_sortedKeyList_clear_is_nil (impl : RepoImpl) : Prop :=
  impl.sortedcontainersCore.sortedKeyListClear (α := Nat) [1, 2, 3] = [] ∧
  impl.sortedcontainersCore.sortedKeyListClear (α := Nat) [] = []

/-- `contains` on a `SortedKeyList` built via `mk` correctly reports membership. -/
def spec_sortedKeyList_contains_after_mk (impl : RepoImpl) : Prop :=
  let s := impl.sortedcontainersCore.sortedKeyListMk (α := Nat) [3, 1, 2]
  impl.sortedcontainersCore.sortedKeyListContains s 2 = true ∧
  impl.sortedcontainersCore.sortedKeyListContains s 5 = false

/-- `copy` is the identity in the functional model. -/
def spec_sortedKeyList_copy_is_id (impl : RepoImpl) : Prop :=
  let s : List Nat := [1, 2, 3]
  impl.sortedcontainersCore.sortedKeyListCopy s = s ∧
  impl.sortedcontainersCore.sortedKeyListCopy ([] : List Nat) = []

/-- `count` returns the number of occurrences (= bisect_right − bisect_left). -/
def spec_sortedKeyList_count_concrete (impl : RepoImpl) : Prop :=
  let s := impl.sortedcontainersCore.sortedKeyListMk (α := Nat) [1, 2, 2, 4]
  impl.sortedcontainersCore.sortedKeyListCount s 2 = 2 ∧
  impl.sortedcontainersCore.sortedKeyListCount s 3 = 0 ∧
  impl.sortedcontainersCore.sortedKeyListCount s 1 = 1

/-- `discard` removes one occurrence of the value; absent value is a no-op. -/
def spec_sortedKeyList_discard_concrete (impl : RepoImpl) : Prop :=
  let s := impl.sortedcontainersCore.sortedKeyListMk (α := Nat) [1, 2, 3]
  impl.sortedcontainersCore.sortedKeyListDiscard s 2 = [1, 3] ∧
  impl.sortedcontainersCore.sortedKeyListDiscard s 5 = [1, 2, 3]

/-- `index s v start stop` returns the position of `v` in `[start, stop)`, or `stop` if not
found. -/
def spec_sortedKeyList_index_concrete (impl : RepoImpl) : Prop :=
  let s := impl.sortedcontainersCore.sortedKeyListMk (α := Nat) [1, 2, 3, 4]
  impl.sortedcontainersCore.sortedKeyListIndex s 3 0 4 = 2 ∧
  impl.sortedcontainersCore.sortedKeyListIndex s 5 0 4 = 4

/-- In this Lean model the key function is not stored, so `irange_key` delegates to `irange`
with the same arguments — they are observationally equal. -/
def spec_sortedKeyList_irangeKey_eq_irange (impl : RepoImpl) : Prop :=
  let s : List Nat := [1, 2, 3, 4, 5]
  impl.sortedcontainersCore.sortedKeyListIrangeKey s 2 4 true false =
  impl.sortedcontainersCore.sortedKeyListIrange s 2 4 true false ∧
  impl.sortedcontainersCore.sortedKeyListIrangeKey s 1 5 false true =
  impl.sortedcontainersCore.sortedKeyListIrange s 1 5 false true

/-- `irange` on a `SortedKeyList` extracts elements in a value range. -/
def spec_sortedKeyList_irange_concrete (impl : RepoImpl) : Prop :=
  let s := impl.sortedcontainersCore.sortedKeyListMk (α := Nat) [1, 2, 3, 4, 5]
  impl.sortedcontainersCore.sortedKeyListIrange s 2 4 true false = [2, 3, 4] ∧
  impl.sortedcontainersCore.sortedKeyListIrange s 2 4 false false = [3]

/-- `SortedKeyList.mk` sorts its input in ascending order (by natural `Ord`, duplicates
preserved). -/
def spec_sortedKeyList_mk_sorts (impl : RepoImpl) : Prop :=
  impl.sortedcontainersCore.sortedKeyListMk (α := Nat) [3, 1, 2, 1] = [1, 1, 2, 3] ∧
  impl.sortedcontainersCore.sortedKeyListMk (α := Nat) [] = []

/-- On present values, `remove` and `discard` remove the same occurrence for `SortedKeyList`.
Absent-value Python error behavior is not representable in this pure Lean signature. -/
def spec_sortedKeyList_remove_eq_discard (impl : RepoImpl) : Prop :=
  ∀ (s : List Nat) (x : Nat),
    impl.sortedcontainersCore.sortedKeyListContains s x = true →
      impl.sortedcontainersCore.sortedKeyListRemove s x =
        impl.sortedcontainersCore.sortedKeyListDiscard s x

/-- `update s xs` merges and re-sorts `s` with `xs`. -/
def spec_sortedKeyList_update_concrete (impl : RepoImpl) : Prop :=
  let s : List Nat := [1, 3, 5]
  impl.sortedcontainersCore.sortedKeyListUpdate s [2, 4] = [1, 2, 3, 4, 5] ∧
  impl.sortedcontainersCore.sortedKeyListUpdate s [] = [1, 3, 5]

/-- `add s v` inserts `v` into its sorted position; duplicate values are allowed and produce
consecutive equal elements. -/
def spec_sortedList_add_concrete (impl : RepoImpl) : Prop :=
  let s := impl.sortedcontainersCore.sortedListMk (α := Nat) [1, 3, 5]
  impl.sortedcontainersCore.sortedListAdd s 2 = [1, 2, 3, 5] ∧
  impl.sortedcontainersCore.sortedListAdd s 3 = [1, 3, 3, 5] ∧
  impl.sortedcontainersCore.sortedListAdd ([] : List Nat) 7 = [7]

/-- `add` always increments the length by exactly 1 (duplicates are allowed so no
uniqueness-guard applies). -/
def spec_sortedList_add_increments_len (impl : RepoImpl) : Prop :=
  let s : List Nat := [1, 3, 5]
  impl.sortedcontainersCore.sortedListLen
    (impl.sortedcontainersCore.sortedListAdd s 2) =
  impl.sortedcontainersCore.sortedListLen s + 1 ∧
  impl.sortedcontainersCore.sortedListLen
    (impl.sortedcontainersCore.sortedListAdd s 3) =
  impl.sortedcontainersCore.sortedListLen s + 1

/-- After adding value `v` to any sorted list, `contains` returns `true` for `v`. -/
def spec_sortedList_add_then_contains (impl : RepoImpl) : Prop :=
  let s : List Nat := [1, 3, 5]
  impl.sortedcontainersCore.sortedListContains
    (impl.sortedcontainersCore.sortedListAdd s 2) 2 = true ∧
  impl.sortedcontainersCore.sortedListContains
    (impl.sortedcontainersCore.sortedListAdd ([] : List Nat) 7) 7 = true

/-- `bisect_left s v` returns the leftmost insertion point for `v` — the first index `i` such
that `s[i] ≥ v`. -/
def spec_sortedList_bisectLeft_concrete (impl : RepoImpl) : Prop :=
  let s := impl.sortedcontainersCore.sortedListMk (α := Nat) [1, 2, 2, 3]
  impl.sortedcontainersCore.sortedListBisectLeft s 2 = 1 ∧
  impl.sortedcontainersCore.sortedListBisectLeft s 0 = 0 ∧
  impl.sortedcontainersCore.sortedListBisectLeft s 4 = 4

/-- `bisect_right s v` returns the rightmost insertion point — the first index `i` such that
`s[i] > v`. -/
def spec_sortedList_bisectRight_concrete (impl : RepoImpl) : Prop :=
  let s := impl.sortedcontainersCore.sortedListMk (α := Nat) [1, 2, 2, 3]
  impl.sortedcontainersCore.sortedListBisectRight s 2 = 3 ∧
  impl.sortedcontainersCore.sortedListBisectRight s 0 = 0 ∧
  impl.sortedcontainersCore.sortedListBisectRight s 4 = 4

/-- `clear` returns the empty list regardless of the input. -/
def spec_sortedList_clear_is_nil (impl : RepoImpl) : Prop :=
  impl.sortedcontainersCore.sortedListClear (α := Nat) [1, 2, 3] = [] ∧
  impl.sortedcontainersCore.sortedListClear (α := Nat) [] = []

/-- After constructing a sorted list via `mk`, `contains` correctly reports `true` for elements
present in the input and `false` for absent ones. -/
def spec_sortedList_contains_after_mk (impl : RepoImpl) : Prop :=
  let s := impl.sortedcontainersCore.sortedListMk (α := Nat) [3, 1, 2]
  impl.sortedcontainersCore.sortedListContains s 2 = true ∧
  impl.sortedcontainersCore.sortedListContains s 5 = false

/-- `copy s = s` — the functional model has no distinction between deep and shallow copy. -/
def spec_sortedList_copy_is_id (impl : RepoImpl) : Prop :=
  let s : List Nat := [1, 2, 3]
  impl.sortedcontainersCore.sortedListCopy s = s ∧
  impl.sortedcontainersCore.sortedListCopy ([] : List Nat) = []

/-- `delitem i s` removes the element at index `i`; on OOB index it is a no-op. -/
def spec_sortedList_delitem_concrete (impl : RepoImpl) : Prop :=
  let s := impl.sortedcontainersCore.sortedListMk (α := Nat) [1, 2, 3]
  impl.sortedcontainersCore.sortedListDelitem s 1 = [1, 3] ∧
  impl.sortedcontainersCore.sortedListDelitem s 5 = [1, 2, 3]

/-- `discard s v` removes the first occurrence of `v`; if `v` is absent the list is returned
unchanged. -/
def spec_sortedList_discard_concrete (impl : RepoImpl) : Prop :=
  let s := impl.sortedcontainersCore.sortedListMk (α := Nat) [1, 2, 2, 3]
  impl.sortedcontainersCore.sortedListDiscard s 2 = [1, 2, 3] ∧
  impl.sortedcontainersCore.sortedListDiscard s 5 = [1, 2, 2, 3]

/-- `getitem` at a valid index returns the element at that sorted position; out-of-bounds returns
`default` (0 for `Nat`). -/
def spec_sortedList_getitem_concrete (impl : RepoImpl) : Prop :=
  let s := impl.sortedcontainersCore.sortedListMk (α := Nat) [3, 1, 2]
  impl.sortedcontainersCore.sortedListGetitem s 0 = 1 ∧
  impl.sortedcontainersCore.sortedListGetitem s 2 = 3 ∧
  impl.sortedcontainersCore.sortedListGetitem s 5 = 0

/-- `index s v start stop` returns the position of `v` in `[start, stop)` when present, and
`stop` when absent or out-of-range. -/
def spec_sortedList_index_concrete (impl : RepoImpl) : Prop :=
  let s := impl.sortedcontainersCore.sortedListMk (α := Nat) [1, 2, 3, 4]
  impl.sortedcontainersCore.sortedListIndex s 3 0 4 = 2 ∧
  impl.sortedcontainersCore.sortedListIndex s 5 0 4 = 4 ∧
  impl.sortedcontainersCore.sortedListIndex s 1 2 4 = 4

/-- `irange s min max inclusive reverse` extracts elements between `min` and `max`. When
`inclusive=true` both endpoints are included; when `false` both are excluded. The `reverse` flag
reverses the result. -/
def spec_sortedList_irange_concrete (impl : RepoImpl) : Prop :=
  let s := impl.sortedcontainersCore.sortedListMk (α := Nat) [1, 2, 3, 4, 5]
  impl.sortedcontainersCore.sortedListIrange s 2 4 true false = [2, 3, 4] ∧
  impl.sortedcontainersCore.sortedListIrange s 2 4 true true  = [4, 3, 2] ∧
  impl.sortedcontainersCore.sortedListIrange s 2 4 false false = [3]

/-- `islice s start stop reverse` is a position-based slice `[start, stop)`, optionally
reversed. -/
def spec_sortedList_islice_concrete (impl : RepoImpl) : Prop :=
  let s := impl.sortedcontainersCore.sortedListMk (α := Nat) [1, 2, 3, 4, 5]
  impl.sortedcontainersCore.sortedListIslice s 1 3 false = [2, 3] ∧
  impl.sortedcontainersCore.sortedListIslice s 1 3 true  = [3, 2] ∧
  impl.sortedcontainersCore.sortedListIslice s 0 0 false = []

/-- `iter s = s` — iteration yields the sorted underlying list unchanged. -/
def spec_sortedList_iter_eq_underlying (impl : RepoImpl) : Prop :=
  let s := impl.sortedcontainersCore.sortedListMk (α := Nat) [3, 1, 2]
  impl.sortedcontainersCore.sortedListIter s = s ∧
  impl.sortedcontainersCore.sortedListIter ([] : List Nat) = []

/-- `len` returns the number of elements; duplicates are preserved so `mk [1,1,2]` has length 3. -/
def spec_sortedList_len_concrete (impl : RepoImpl) : Prop :=
  impl.sortedcontainersCore.sortedListLen
    (impl.sortedcontainersCore.sortedListMk (α := Nat) [3, 1, 2, 1]) = 4 ∧
  impl.sortedcontainersCore.sortedListLen
    (impl.sortedcontainersCore.sortedListMk (α := Nat) []) = 0

/-- `mk` on an unsorted or duplicate-containing list returns the sorted permutation in ascending
order. On the empty list it returns `[]`. -/
def spec_sortedList_mk_sorts (impl : RepoImpl) : Prop :=
  impl.sortedcontainersCore.sortedListMk (α := Nat) [3, 1, 2, 1] = [1, 1, 2, 3] ∧
  impl.sortedcontainersCore.sortedListMk (α := Nat) [] = [] ∧
  impl.sortedcontainersCore.sortedListMk (α := Nat) [5] = [5]

/-- In the pure model, `pop` returns the value at index `i` without removing it — identical to
`getitem`. -/
def spec_sortedList_pop_eq_getitem (impl : RepoImpl) : Prop :=
  let s : List Nat := [1, 2, 3, 4]
  impl.sortedcontainersCore.sortedListPop s 0 =
  impl.sortedcontainersCore.sortedListGetitem s 0 ∧
  impl.sortedcontainersCore.sortedListPop s 3 =
  impl.sortedcontainersCore.sortedListGetitem s 3 ∧
  impl.sortedcontainersCore.sortedListPop s 9 =
  impl.sortedcontainersCore.sortedListGetitem s 9

/-- On present values, `remove` and `discard` remove the same occurrence for `SortedList`.
Absent-value Python error behavior is not representable in this pure Lean signature. -/
def spec_sortedList_remove_eq_discard (impl : RepoImpl) : Prop :=
  ∀ (s : SortedContainers.SortedList Nat) (x : Nat),
    impl.sortedcontainersCore.sortedListContains s x = true →
      impl.sortedcontainersCore.sortedListRemove s x =
        impl.sortedcontainersCore.sortedListDiscard s x

/-- `reversed s = (iter s).reverse` — the reversed iterator is exactly the reverse of the forward
iterator. -/
def spec_sortedList_reversed_eq_iterRev (impl : RepoImpl) : Prop :=
  let s : List Nat := [1, 2, 3, 4]
  impl.sortedcontainersCore.sortedListReversed s =
  (impl.sortedcontainersCore.sortedListIter s).reverse ∧
  impl.sortedcontainersCore.sortedListReversed ([] : List Nat) = []

/-- `update s xs` inserts all elements of `xs` into `s` and returns the fully sorted result. -/
def spec_sortedList_update_concrete (impl : RepoImpl) : Prop :=
  let s := impl.sortedcontainersCore.sortedListMk (α := Nat) [1, 3, 5]
  impl.sortedcontainersCore.sortedListUpdate s [4, 2] = [1, 2, 3, 4, 5] ∧
  impl.sortedcontainersCore.sortedListUpdate s [] = [1, 3, 5]
