import SortedcontainersCore.Spec.Aux

/-!
# SortedcontainersCore.Spec.SortedDict

Structural specifications for `SortedDict` APIs.
Each `spec_*` is a property over an arbitrary `impl : RepoImpl`.
-/

/-- Constructing a dictionary gives sorted keys, and the items/keys/values views agree. -/
def spec_sortedDict_mk_views_law (impl : RepoImpl) : Prop :=
  ∀ pairs : List (Nat × Nat),
    let d := impl.sortedcontainersCore.sortedDictMk (α := Nat) (β := Nat) pairs
    spec_helper_sortedByOrd (impl.sortedcontainersCore.sortedDictKeys d) ∧
    impl.sortedcontainersCore.sortedDictItems d = d ∧
    impl.sortedcontainersCore.sortedDictKeys d =
      (impl.sortedcontainersCore.sortedDictItems d).map Prod.fst ∧
    impl.sortedcontainersCore.sortedDictValues d =
      (impl.sortedcontainersCore.sortedDictItems d).map Prod.snd

/-- Setting a key preserves sorted keys, makes the key present, and makes `pop` return the new
value for that key. -/
def spec_sortedDict_setitem_preserves_key_lookup_and_order (impl : RepoImpl) : Prop :=
  ∀ (d : SortedContainers.SortedDict Nat Nat) (k v default : Nat),
    spec_helper_sortedByOrd (impl.sortedcontainersCore.sortedDictKeys d) →
      spec_helper_sortedByOrd
        (impl.sortedcontainersCore.sortedDictKeys
          (impl.sortedcontainersCore.sortedDictSetitem d k v)) ∧
      k ∈ impl.sortedcontainersCore.sortedDictKeys
        (impl.sortedcontainersCore.sortedDictSetitem d k v) ∧
      impl.sortedcontainersCore.sortedDictPop
        (impl.sortedcontainersCore.sortedDictSetitem d k v) k default = v

/-- Setting one key preserves lookup results for every other key. -/
def spec_sortedDict_setitem_preserves_other_lookups (impl : RepoImpl) : Prop :=
  ∀ (d : SortedContainers.SortedDict Nat Nat) (k other v default : Nat),
    other ≠ k →
      impl.sortedcontainersCore.sortedDictPop
        (impl.sortedcontainersCore.sortedDictSetitem d k v) other default =
      impl.sortedcontainersCore.sortedDictPop d other default

/-- Deleting a key preserves sorted keys, removes the key from the key view, and makes lookup
fall back to the supplied default. -/
def spec_sortedDict_delitem_removes_key_and_preserves_views (impl : RepoImpl) : Prop :=
  ∀ (d : SortedContainers.SortedDict Nat Nat) (k default : Nat),
    spec_helper_sortedByOrd (impl.sortedcontainersCore.sortedDictKeys d) →
      spec_helper_sortedByOrd
        (impl.sortedcontainersCore.sortedDictKeys
          (impl.sortedcontainersCore.sortedDictDelitem d k)) ∧
      k ∉ impl.sortedcontainersCore.sortedDictKeys
        (impl.sortedcontainersCore.sortedDictDelitem d k) ∧
      impl.sortedcontainersCore.sortedDictPop
        (impl.sortedcontainersCore.sortedDictDelitem d k) k default = default ∧
      impl.sortedcontainersCore.sortedDictKeys
        (impl.sortedcontainersCore.sortedDictDelitem d k) =
        (impl.sortedcontainersCore.sortedDictItems
          (impl.sortedcontainersCore.sortedDictDelitem d k)).map Prod.fst

/-- Deleting one key preserves lookup results for every other key. -/
def spec_sortedDict_delitem_preserves_other_lookups (impl : RepoImpl) : Prop :=
  ∀ (d : SortedContainers.SortedDict Nat Nat) (k other default : Nat),
    other ≠ k →
      impl.sortedcontainersCore.sortedDictPop
        (impl.sortedcontainersCore.sortedDictDelitem d k) other default =
      impl.sortedcontainersCore.sortedDictPop d other default

/-- `setdefault` is a no-op for present keys and inserts the default for absent keys. -/
def spec_sortedDict_setdefault_laws (impl : RepoImpl) : Prop :=
  ∀ (d : SortedContainers.SortedDict Nat Nat) (k v default : Nat),
    spec_helper_sortedByOrd (impl.sortedcontainersCore.sortedDictKeys d) →
      (k ∈ impl.sortedcontainersCore.sortedDictKeys d →
        impl.sortedcontainersCore.sortedDictSetdefault d k v = d) ∧
      (k ∉ impl.sortedcontainersCore.sortedDictKeys d →
        impl.sortedcontainersCore.sortedDictPop
          (impl.sortedcontainersCore.sortedDictSetdefault d k v) k default = v ∧
        spec_helper_sortedByOrd
          (impl.sortedcontainersCore.sortedDictKeys
            (impl.sortedcontainersCore.sortedDictSetdefault d k v)))

/-- Iteration, reversed iteration, and item-at-index APIs agree with the dictionary views. -/
def spec_sortedDict_iteration_and_item_views (impl : RepoImpl) : Prop :=
  ∀ (d : SortedContainers.SortedDict Nat Nat) (i : Nat),
    impl.sortedcontainersCore.sortedDictIter d =
      impl.sortedcontainersCore.sortedDictKeys d ∧
    impl.sortedcontainersCore.sortedDictReversed d =
      (impl.sortedcontainersCore.sortedDictKeys d).reverse ∧
    impl.sortedcontainersCore.sortedDictPeekitem d i =
      impl.sortedcontainersCore.sortedDictPopitem d i

-- ── Restored from backup (T1B over-trim recovery) ──────────────────────

/-- Keys of a key-value list. -/
def spec_helper_keysOf (pairs : List (Nat × Nat)) : List Nat := pairs.map Prod.fst

/-- `clear` returns the empty dict. -/
def spec_sortedDict_clear_is_nil (impl : RepoImpl) : Prop :=
  impl.sortedcontainersCore.sortedDictClear (α := Nat) (β := Nat) [(1, 10), (2, 20)] = [] ∧
  impl.sortedcontainersCore.sortedDictClear (α := Nat) (β := Nat) [] = []

/-- `copy` is the identity. -/
def spec_sortedDict_copy_is_id (impl : RepoImpl) : Prop :=
  let d : List (Nat × Nat) := [(1, 10), (2, 20)]
  impl.sortedcontainersCore.sortedDictCopy d = d ∧
  impl.sortedcontainersCore.sortedDictCopy ([] : List (Nat × Nat)) = []

/-- `delitem d k` removes the entry for key `k`; absent key is a no-op. -/
def spec_sortedDict_delitem_removes_key (impl : RepoImpl) : Prop :=
  let d := impl.sortedcontainersCore.sortedDictMk (α := Nat) (β := Nat)
            [(1, 10), (2, 20), (3, 30)]
  impl.sortedcontainersCore.sortedDictDelitem d 2 = [(1, 10), (3, 30)] ∧
  impl.sortedcontainersCore.sortedDictDelitem d 9 = [(1, 10), (2, 20), (3, 30)]

/-- After deleting key `k`, `pop d k dflt` returns `dflt` (key is absent). -/
def spec_sortedDict_delitem_then_pop_default (impl : RepoImpl) : Prop :=
  let d : List (Nat × Nat) := [(1, 10), (2, 20), (3, 30)]
  impl.sortedcontainersCore.sortedDictPop
    (impl.sortedcontainersCore.sortedDictDelitem d 2) 2 0 = 0 ∧
  impl.sortedcontainersCore.sortedDictPop
    (impl.sortedcontainersCore.sortedDictDelitem d 2) 1 0 = 10

/-- `items d = d` — the items view is the underlying sorted key-value list. -/
def spec_sortedDict_items_eq_underlying (impl : RepoImpl) : Prop :=
  let d := impl.sortedcontainersCore.sortedDictMk (α := Nat) (β := Nat)
            [(3, 30), (1, 10), (2, 20)]
  impl.sortedcontainersCore.sortedDictItems d = [(1, 10), (2, 20), (3, 30)] ∧
  impl.sortedcontainersCore.sortedDictItems ([] : List (Nat × Nat)) = []

/-- `iter d = keys d` — iterating a `SortedDict` yields the sorted key list. -/
def spec_sortedDict_iter_eq_keys (impl : RepoImpl) : Prop :=
  let d : List (Nat × Nat) := [(1, 10), (2, 20), (3, 30)]
  impl.sortedcontainersCore.sortedDictIter d =
  impl.sortedcontainersCore.sortedDictKeys d ∧
  impl.sortedcontainersCore.sortedDictIter ([] : List (Nat × Nat)) =
  impl.sortedcontainersCore.sortedDictKeys ([] : List (Nat × Nat))

/-- `keys d = (items d).map Prod.fst`. -/
def spec_sortedDict_keys_eq_itemsFirst (impl : RepoImpl) : Prop :=
  let d : List (Nat × Nat) := [(1, 10), (2, 20), (3, 30)]
  impl.sortedcontainersCore.sortedDictKeys d =
  (impl.sortedcontainersCore.sortedDictItems d).map Prod.fst

/-- `mk pairs` builds a sorted dictionary: duplicate keys use the *last* value (left-to-right
fold semantics), and the result is sorted ascending by key. -/
def spec_sortedDict_mk_sort_dedup_lastWins (impl : RepoImpl) : Prop :=
  impl.sortedcontainersCore.sortedDictMk (α := Nat) (β := Nat)
    [(3, 10), (1, 20), (3, 30), (2, 40)] = [(1, 20), (2, 40), (3, 30)] ∧
  impl.sortedcontainersCore.sortedDictMk (α := Nat) (β := Nat) [] = []

/-- In the pure model, `peekitem` and `popitem` are identical — both return the pair at position
`i` without modifying the dict. -/
def spec_sortedDict_peekitem_eq_popitem (impl : RepoImpl) : Prop :=
  let d : List (Nat × Nat) := [(1, 10), (2, 20), (3, 30)]
  impl.sortedcontainersCore.sortedDictPeekitem d 1 =
  impl.sortedcontainersCore.sortedDictPopitem d 1 ∧
  impl.sortedcontainersCore.sortedDictPeekitem d 9 =
  impl.sortedcontainersCore.sortedDictPopitem d 9

/-- `pop d k dflt` returns `dflt` when `k` is not in the dict. -/
def spec_sortedDict_pop_absent_default (impl : RepoImpl) : Prop :=
  let d : List (Nat × Nat) := [(1, 10), (3, 30)]
  impl.sortedcontainersCore.sortedDictPop d 2 99 = 99 ∧
  impl.sortedcontainersCore.sortedDictPop ([] : List (Nat × Nat)) 5 42 = 42

/-- `pop d k default` returns the value for key `k` when present. -/
def spec_sortedDict_pop_concrete (impl : RepoImpl) : Prop :=
  let d := impl.sortedcontainersCore.sortedDictMk (α := Nat) (β := Nat)
            [(1, 10), (2, 20), (3, 30)]
  impl.sortedcontainersCore.sortedDictPop d 2 0 = 20 ∧
  impl.sortedcontainersCore.sortedDictPop d 1 0 = 10

/-- `popitem d i` returns the key-value pair at position `i` in sorted order. OOB returns
`(default, default) = (0, 0)`. -/
def spec_sortedDict_popitem_concrete (impl : RepoImpl) : Prop :=
  let d := impl.sortedcontainersCore.sortedDictMk (α := Nat) (β := Nat)
            [(3, 30), (1, 10), (2, 20)]
  impl.sortedcontainersCore.sortedDictPopitem d 0 = (1, 10) ∧
  impl.sortedcontainersCore.sortedDictPopitem d 2 = (3, 30) ∧
  impl.sortedcontainersCore.sortedDictPopitem d 9 = (0, 0)

/-- `reversed d = (keys d).reverse` — reversed iteration yields the key list in descending
order. -/
def spec_sortedDict_reversed_eq_keysRev (impl : RepoImpl) : Prop :=
  let d : List (Nat × Nat) := [(1, 10), (2, 20), (3, 30)]
  impl.sortedcontainersCore.sortedDictReversed d =
  (impl.sortedcontainersCore.sortedDictKeys d).reverse

/-- `setdefault d k dflt` inserts `(k, dflt)` when `k` is absent; the subsequent `pop` returns
`dflt`. -/
def spec_sortedDict_setdefault_absent_inserts (impl : RepoImpl) : Prop :=
  let d := impl.sortedcontainersCore.sortedDictMk (α := Nat) (β := Nat)
            [(1, 10), (3, 30)]
  let d' := impl.sortedcontainersCore.sortedDictSetdefault d 2 99
  impl.sortedcontainersCore.sortedDictPop d' 2 0 = 99 ∧
  impl.sortedcontainersCore.sortedDictPop d' 1 0 = 10

/-- `setdefault d k dflt` leaves the dict unchanged when `k` is already present. -/
def spec_sortedDict_setdefault_present_noop (impl : RepoImpl) : Prop :=
  let d := impl.sortedcontainersCore.sortedDictMk (α := Nat) (β := Nat)
            [(1, 10), (2, 20), (3, 30)]
  impl.sortedcontainersCore.sortedDictSetdefault d 2 99 = d ∧
  impl.sortedcontainersCore.sortedDictSetdefault d 1 0 = d

/-- `setitem d k v` inserts or updates key `k` with value `v`, maintaining sorted key order. -/
def spec_sortedDict_setitem_concrete (impl : RepoImpl) : Prop :=
  let d := impl.sortedcontainersCore.sortedDictMk (α := Nat) (β := Nat)
            [(1, 10), (3, 30)]
  impl.sortedcontainersCore.sortedDictSetitem d 2 20 = [(1, 10), (2, 20), (3, 30)] ∧
  impl.sortedcontainersCore.sortedDictSetitem d 3 99 = [(1, 10), (3, 99)]

/-- After `setitem d k v`, `pop (setitem d k v) k default = v` — the inserted value is
retrievable. -/
def spec_sortedDict_setitem_then_pop (impl : RepoImpl) : Prop :=
  let d : List (Nat × Nat) := [(1, 10), (3, 30)]
  impl.sortedcontainersCore.sortedDictPop
    (impl.sortedcontainersCore.sortedDictSetitem d 2 20) 2 0 = 20 ∧
  impl.sortedcontainersCore.sortedDictPop
    (impl.sortedcontainersCore.sortedDictSetitem d 1 99) 1 0 = 99

/-- `values d = (items d).map Prod.snd`. -/
def spec_sortedDict_values_eq_itemsSecond (impl : RepoImpl) : Prop :=
  let d : List (Nat × Nat) := [(1, 10), (2, 20), (3, 30)]
  impl.sortedcontainersCore.sortedDictValues d =
  (impl.sortedcontainersCore.sortedDictItems d).map Prod.snd

-- ── Manual PR-35 ports (stand-alone) ───────────────────────────────────

/-- PR-35 Spec 12 (manual): for *every* sorted dictionary the keys view equals the first
projection of the items view. The existing `spec_sortedDict_mk_views_law` only asserts this for
freshly built `mk pairs`; this stand-alone law lifts the obligation to arbitrary `(d : SortedDict
…)` so it can be reused as a separate joint-unsat antecedent. -/
def spec_sortedDict_keys_agree_with_items (impl : RepoImpl) : Prop :=
  ∀ d : SortedContainers.SortedDict Nat Nat,
    impl.sortedcontainersCore.sortedDictKeys d =
      (impl.sortedcontainersCore.sortedDictItems d).map Prod.fst
