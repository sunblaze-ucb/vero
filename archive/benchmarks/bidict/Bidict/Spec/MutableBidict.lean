import Bidict.Harness

/-!
# Bidict.Spec.MutableBidict

Specifications for mutable bidict operations (`initMutableBidict`,
`delItem`, `setItem`, `forceput`, `clear`, `pop`, `popitem`,
`update`, `forceupdate`, `putall`).
Each `spec_*` is a property over an arbitrary `impl : RepoImpl`.

DO NOT MODIFY — frozen curator-given content.
-/

/-- No duplicate keys occur in the bidict data. -/
def spec_helper_noDuplicateKeys : BidictBase Nat String → Prop
  | [] => True
  | (k, _) :: rest =>
      rest.any (fun item => item.1 == k) = false ∧ spec_helper_noDuplicateKeys rest

/-- No duplicate values occur in the bidict data. -/
def spec_helper_noDuplicateValues : BidictBase Nat String → Prop
  | [] => True
  | (_, v) :: rest =>
      rest.any (fun item => item.2 == v) = false ∧ spec_helper_noDuplicateValues rest

/-- A bidict is one-to-one when keys and values are both unique. -/
def spec_helper_isOneToOne (data : BidictBase Nat String) : Prop :=
  spec_helper_noDuplicateKeys data ∧ spec_helper_noDuplicateValues data

/-- `initMutableBidict` stores the given data list and `OnDup` policy directly
    in the `data` and `ondup` fields of the resulting `MutableBidict`. -/
def spec_initMutableBidict_fields (impl : RepoImpl) : Prop :=
  ∀ (data : BidictBase Nat String) (od : OnDup),
    let mb := impl.bidict.initMutableBidict data od
    mb.data = data ∧ mb.ondup = od

/-- Deleting a key that is not present returns the bidict unchanged. -/
def spec_delItem_absent_noop (impl : RepoImpl) : Prop :=
  ∀ (mb : MutableBidict Nat String) (key : Nat),
    key ∉ mb.data.map Prod.fst →
    impl.bidict.delItem mb key = mb

/-- Deleting a present key removes exactly that entry; remaining entries are
    unchanged. -/
def spec_delItem_removes_key (impl : RepoImpl) : Prop :=
  ∀ (mb : MutableBidict Nat String) (key : Nat),
    (impl.bidict.delItem mb key).data =
      mb.data.filter (fun (k, _) => !(k == key))

/-- With the `raise` policy, inserting a fresh key-value pair succeeds with
    the new pair appended. -/
def spec_setItem_ok_inserts (impl : RepoImpl) : Prop :=
  ∀ (mb : MutableBidict Nat String) (key : Nat) (val : String),
    key ∉ mb.data.map Prod.fst →
    val ∉ mb.data.map Prod.snd →
    impl.bidict.setItem mb key val =
      Except.ok { mb with data := mb.data ++ [(key, val)] }

/-- With the `raise` policy, inserting an entry whose key already exists
    raises `duplicateKeyError`. -/
def spec_setItem_keydup_raises (impl : RepoImpl) : Prop :=
  ∀ (mb : MutableBidict Nat String) (key : Nat) (val : String),
    key ∈ mb.data.map Prod.fst →
    mb.ondup.key = OnDupAction.raise →
    impl.bidict.setItem mb key val =
      Except.error DuplicationError.duplicateKeyError

/-- With key-duplicate policy `raise`, any existing key causes `duplicateKeyError`. -/
def spec_setItem_keydup_raises_universal (impl : RepoImpl) : Prop :=
  ∀ (mb : MutableBidict Nat String) (key : Nat) (newVal : String),
    key ∈ mb.data.map Prod.fst →
    mb.ondup.key = OnDupAction.raise →
      impl.bidict.setItem mb key newVal =
        Except.error DuplicationError.duplicateKeyError

/-- With value-duplicate policy `raise`, any existing value causes `duplicateValueError`
    when there is no raised key conflict. -/
def spec_setItem_valuedup_raises_universal (impl : RepoImpl) : Prop :=
  ∀ (mb : MutableBidict Nat String) (key : Nat) (val : String),
    key ∉ mb.data.map Prod.fst →
    val ∈ mb.data.map Prod.snd →
    mb.ondup.val = OnDupAction.raise →
      impl.bidict.setItem mb key val =
        Except.error DuplicationError.duplicateValueError

/-- With the `dropNew` policy for both key and value, inserting a duplicate
    key silently returns the bidict unchanged. -/
def spec_setItem_dropNew_unchanged (impl : RepoImpl) : Prop :=
  ∀ (mb : MutableBidict Nat String) (key : Nat) (val : String),
    key ∈ mb.data.map Prod.fst →
    mb.ondup.key = OnDupAction.dropNew →
    impl.bidict.setItem mb key val = Except.ok mb

/-- When the key already exists, `forceput` updates its value in-place. -/
def spec_forceput_overwrites_existing (impl : RepoImpl) : Prop :=
  ∀ (mb : MutableBidict Nat String) (key : Nat) (val : String),
    key ∈ mb.data.map Prod.fst →
    let cleaned := mb.data.filter (fun (k, v) => k == key || !(v == val))
    impl.bidict.forceput mb key val =
      { mb with data :=
        cleaned.map (fun (k, v) => if k == key then (k, val) else (k, v)) }

/-- When the key is absent, `forceput` appends the new `(key, val)` pair. -/
def spec_forceput_inserts_new (impl : RepoImpl) : Prop :=
  ∀ (mb : MutableBidict Nat String) (key : Nat) (val : String),
    key ∉ mb.data.map Prod.fst →
    impl.bidict.forceput mb key val =
      { mb with data := mb.data.filter (fun (_, v) => !(v == val)) ++ [(key, val)] }

/-- `clear` empties the `data` field of any `MutableBidict`, regardless of
    its contents or `ondup` policy. -/
def spec_clear_empty_data (impl : RepoImpl) : Prop :=
  ∀ (mb : MutableBidict Nat String),
    (impl.bidict.clear mb).data = []

/-- When the key is present, `pop` returns the updated bidict (with that entry
    removed) and `Sum.inl v` carrying the found value. -/
def spec_pop_present (impl : RepoImpl) : Prop :=
  ∀ {DT : Type} (mb : MutableBidict Nat String) (key : Nat) (default : DT),
    impl.bidict.pop mb key default =
      match mb.data.find? (fun (k, _) => k == key) with
      | some (_, v) =>
          ({ mb with data := mb.data.filter (fun (k, _) => !(k == key)) },
           Sum.inl v)
      | none => (mb, Sum.inr default)

/-- When the key is absent, `pop` returns the bidict unchanged and `Sum.inr
    default` carrying the supplied default value. -/
def spec_pop_absent (impl : RepoImpl) : Prop :=
  ∀ {DT : Type} (mb : MutableBidict Nat String) (key : Nat) (default : DT),
    key ∉ mb.data.map Prod.fst →
    impl.bidict.pop mb key default = (mb, Sum.inr default)

/-- `popitem` on an empty bidict returns `none`. -/
def spec_popitem_empty (impl : RepoImpl) : Prop :=
  let mb : MutableBidict Nat String :=
    { data := [], ondup := { key := OnDupAction.raise, val := OnDupAction.raise } }
  impl.bidict.popitem mb = none

/-- `popitem` on a non-empty bidict removes and returns the first (head)
    entry, with the remaining entries in the updated bidict. -/
def spec_popitem_nonempty (impl : RepoImpl) : Prop :=
  ∀ (mb : MutableBidict Nat String) (item : Nat × String) (rest : BidictBase Nat String),
    mb.data = item :: rest →
    impl.bidict.popitem mb = some ({ mb with data := rest }, item)

/-- With the `raise` policy, `update` with a non-conflicting list succeeds and
    appends the new entries in order. -/
def spec_update_ok_appends (impl : RepoImpl) : Prop :=
  ∀ (mb : MutableBidict Nat String) (other : BidictBase Nat String),
    impl.bidict.update mb other =
      other.foldl (fun acc (k, v) =>
        match acc with
        | Except.error e => Except.error e
        | Except.ok mb' => impl.bidict.setItem mb' k v) (Except.ok mb)

/-- `forceupdate` with a list of new key-value pairs (no existing keys) appends
    each pair in order, never raising an error. -/
def spec_forceupdate_appends (impl : RepoImpl) : Prop :=
  ∀ (mb : MutableBidict Nat String) (other : BidictBase Nat String),
    impl.bidict.forceupdate mb other =
      other.foldl (fun acc (k, v) => impl.bidict.forceput acc k v) mb

/-- `putall` uses a caller-supplied `mergeOndup` during the merge, then
    restores the original `ondup` policy. Frame condition: `ondup` is unchanged. -/
def spec_putall_preserves_ondup (impl : RepoImpl) : Prop :=
  ∀ (mb : MutableBidict Nat String) (other : BidictBase Nat String) (mergeOd : OnDup),
    (impl.bidict.putall mb other mergeOd).ondup = mb.ondup

/-- Successful `setItem` preserves the one-to-one bidict invariant. -/
def spec_setItem_preserves_one_to_one (impl : RepoImpl) : Prop :=
  ∀ (mb next : MutableBidict Nat String) (key : Nat) (val : String),
    spec_helper_isOneToOne mb.data →
    impl.bidict.setItem mb key val = Except.ok next →
      spec_helper_isOneToOne next.data

/-- `forceput` preserves the one-to-one bidict invariant. -/
def spec_forceput_preserves_one_to_one (impl : RepoImpl) : Prop :=
  ∀ (mb : MutableBidict Nat String) (key : Nat) (val : String),
    spec_helper_isOneToOne mb.data →
      spec_helper_isOneToOne (impl.bidict.forceput mb key val).data

/-- `putall` preserves the one-to-one bidict invariant when both inputs are one-to-one. -/
def spec_putall_preserves_one_to_one (impl : RepoImpl) : Prop :=
  ∀ (mb : MutableBidict Nat String) (other : BidictBase Nat String) (mergeOd : OnDup),
    spec_helper_isOneToOne mb.data →
    spec_helper_isOneToOne other →
      spec_helper_isOneToOne (impl.bidict.putall mb other mergeOd).data

/-- Frame: clearing absorbs any `delItem` effect — `clear ∘ delItem _ = clear`,
    universally over the bidict and the deletion key. -/
def spec_delItem_then_clear (impl : RepoImpl) : Prop :=
  ∀ (mb : MutableBidict Nat String) (key : Nat),
    impl.bidict.clear (impl.bidict.delItem mb key) = impl.bidict.clear mb

/-- `forceput` is idempotent on the same key/value: re-applying it leaves the
    bidict unchanged. -/
def spec_forceput_idempotent (impl : RepoImpl) : Prop :=
  ∀ (mb : MutableBidict Nat String) (key : Nat) (val : String),
    impl.bidict.forceput (impl.bidict.forceput mb key val) key val =
      impl.bidict.forceput mb key val

/-- After clearing and force-putting a single `(key, val)`, that pair is the
    one returned by `popitem`; the residual bidict is `clear self`. -/
def spec_forceput_popitem_singleton (impl : RepoImpl) : Prop :=
  ∀ (mb : MutableBidict Nat String) (key : Nat) (val : String),
    impl.bidict.popitem (impl.bidict.forceput (impl.bidict.clear mb) key val) =
      some (impl.bidict.clear mb, (key, val))

/-- `clear` is idempotent: applying it twice gives the same result as once. -/
def spec_clear_idempotent (impl : RepoImpl) : Prop :=
  ∀ (mb : MutableBidict Nat String),
    impl.bidict.clear (impl.bidict.clear mb) = impl.bidict.clear mb

/-- After clearing and successfully `setItem`-ing a single `(key, val)`, that
    pair is returned by `popitem`. Cross-API round-trip: setItem ∘ clear is
    inverted by popitem on the singleton. -/
def spec_setItem_popitem_singleton (impl : RepoImpl) : Prop :=
  ∀ (mb : MutableBidict Nat String) (key : Nat) (val : String),
    match impl.bidict.setItem (impl.bidict.clear mb) key val with
    | Except.ok next =>
        impl.bidict.popitem next = some (impl.bidict.clear mb, (key, val))
    | Except.error _ => False

/-- `forceupdate` is idempotent on the same argument list — applying it twice
    has the same effect as applying it once — when `mb` is a well-formed
    (one-to-one) bidict and `arg` carries no duplicate values. The
    `noDuplicateValues arg` guard is essential: `forceupdate` folds `forceput`,
    which drops any *other* entry sharing an incoming value, so a duplicated
    value in `arg` lets the first pass update an entry in place while the second
    pass drops-and-reappends it, reshuffling order (e.g. `mb = [(0,"a"),(1,"b")]`,
    `arg = [(2,"c"),(0,"c")]` gives `[(0,"c"),(1,"b")]` once but `[(1,"b"),(0,"c")]`
    twice). With distinct argument values the fold reaches a fixed point after one
    pass. -/
def spec_forceupdate_idempotent (impl : RepoImpl) : Prop :=
  ∀ (mb : MutableBidict Nat String) (arg : BidictBase Nat String),
    spec_helper_isOneToOne mb.data →
    spec_helper_noDuplicateValues arg →
    impl.bidict.forceupdate (impl.bidict.forceupdate mb arg) arg =
      impl.bidict.forceupdate mb arg

/-- `putall` is idempotent on the same `(other, mergeOd)` pair — re-running the
    merge leaves the result unchanged — when both inputs are well-formed
    (one-to-one) bidicts and `mergeOd` is non-order-mutating (no `dropOld` on
    either axis). The no-`dropOld` guards are essential: with only `raise` and
    `dropNew`, `setItem` is append-or-no-op and never removes or reorders an
    existing entry, so the second pass sees the same conflicts and is a no-op.
    A `dropOld` policy instead removes old entries during the first pass, which
    changes which entries conflict on the second pass (e.g. `mb = [(0,"a")]`,
    `other = [(0,"b"),(1,"a")]`, `mergeOd = raise/dropOld` gives `[(1,"a")]` once
    but `[(1,"a"),(0,"b")]` twice). -/
def spec_putall_idempotent (impl : RepoImpl) : Prop :=
  ∀ (mb : MutableBidict Nat String) (other : BidictBase Nat String) (mergeOd : OnDup),
    spec_helper_isOneToOne mb.data →
    spec_helper_isOneToOne other →
    mergeOd.key ≠ OnDupAction.dropOld →
    mergeOd.val ≠ OnDupAction.dropOld →
    impl.bidict.putall (impl.bidict.putall mb other mergeOd) other mergeOd =
      impl.bidict.putall mb other mergeOd

/-- After clearing and `putall`-ing a single-entry list `[(key, val)]`, that
    pair is returned by `popitem`. Cross-API round-trip linking putall and
    popitem on the singleton. -/
def spec_putall_popitem_singleton (impl : RepoImpl) : Prop :=
  ∀ (mb : MutableBidict Nat String) (key : Nat) (val : String) (mergeOd : OnDup),
    let cleared := impl.bidict.clear mb
    impl.bidict.popitem (impl.bidict.putall cleared [(key, val)] mergeOd) =
      some (cleared, (key, val))
