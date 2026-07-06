import Bidict.Harness

/-!
# Bidict.Spec.OrderedBidict

Specifications for ordered bidict operations (`initOrderedBidict`,
`iterOrderedBidict`, `inverseOrderedBidict`, `invOrderedBidict`,
`clearOrderedBidict`, `popOrderedBidict`, `popitemOrderedBidict`,
`moveToEndOrderedBidict`, `keysOrderedBidict`, `itemsOrderedBidict`).
Each `spec_*` is a property over an arbitrary `impl : RepoImpl`.

DO NOT MODIFY — frozen curator-given content.
-/

/-- `initOrderedBidict` wraps the given data list directly in an
    `OrderedBidict`; the `data` field equals the input. -/
def spec_initOrderedBidict_data (impl : RepoImpl) : Prop :=
  ∀ (d : BidictBase Nat String),
    (impl.bidict.initOrderedBidict d).data = d

/-- With `reverse = false`, `iterOrderedBidict` returns the same key list as
    `keysOrderedBidict`. -/
def spec_iterOrderedBidict_false_eq_keys (impl : RepoImpl) : Prop :=
  ∀ (od : OrderedBidict Nat String),
    impl.bidict.iterOrderedBidict od false = impl.bidict.keysOrderedBidict od

/-- With `reverse = true`, `iterOrderedBidict` returns the reversed key list
    compared to `keysOrderedBidict`. -/
def spec_iterOrderedBidict_true_eq_reverse (impl : RepoImpl) : Prop :=
  ∀ (od : OrderedBidict Nat String),
    impl.bidict.iterOrderedBidict od true =
      (impl.bidict.keysOrderedBidict od).reverse

/-- `inverseOrderedBidict` maps each `(k, v)` pair to `(v, k)` in the same
    order. -/
def spec_inverseOrderedBidict_swaps (impl : RepoImpl) : Prop :=
  ∀ (od : OrderedBidict Nat String),
    (impl.bidict.inverseOrderedBidict od).data =
      od.data.map (fun item => (item.2, item.1))

/-- Applying `inverseOrderedBidict` twice is the identity. -/
def spec_inverseOrderedBidict_involution (impl : RepoImpl) : Prop :=
  ∀ (od : OrderedBidict Nat String),
    impl.bidict.inverseOrderedBidict (impl.bidict.inverseOrderedBidict od) = od

/-- `invOrderedBidict` is an alias for `inverseOrderedBidict`; they produce
    identical results. -/
def spec_invOrderedBidict_eq_inverseOrderedBidict (impl : RepoImpl) : Prop :=
  ∀ (od : OrderedBidict Nat String),
    impl.bidict.invOrderedBidict od = impl.bidict.inverseOrderedBidict od

/-- `clearOrderedBidict` sets the `data` field to `[]` for any input. -/
def spec_clearOrderedBidict_data_empty (impl : RepoImpl) : Prop :=
  ∀ (od : OrderedBidict Nat String),
    (impl.bidict.clearOrderedBidict od).data = []

/-- When the key exists, `popOrderedBidict` returns `some (updated_od, v)`
    where the entry is removed from the updated ordered bidict. -/
def spec_popOrderedBidict_present (impl : RepoImpl) : Prop :=
  ∀ (od : OrderedBidict Nat String) (key : Nat),
    impl.bidict.popOrderedBidict od key =
      match od.data.find? (fun (k, _) => k == key) with
      | none => none
      | some (_, v) =>
          some ({ data := od.data.filter (fun (k, _) => !(k == key)) }, v)

/-- When the key is absent, `popOrderedBidict` returns `none`. -/
def spec_popOrderedBidict_absent (impl : RepoImpl) : Prop :=
  ∀ (od : OrderedBidict Nat String) (key : Nat),
    key ∉ od.data.map Prod.fst →
    impl.bidict.popOrderedBidict od key = none

/-- `popitemOrderedBidict` on an empty ordered bidict returns `none` regardless
    of the `last` flag. -/
def spec_popitemOrderedBidict_empty (impl : RepoImpl) : Prop :=
  impl.bidict.popitemOrderedBidict
    ({ data := [] } : OrderedBidict Nat String) false = none ∧
  impl.bidict.popitemOrderedBidict
    ({ data := [] } : OrderedBidict Nat String) true = none

/-- With `last = false`, `popitemOrderedBidict` removes and returns the first
    (head) entry. -/
def spec_popitemOrderedBidict_first (impl : RepoImpl) : Prop :=
  ∀ (item : Nat × String) (rest : BidictBase Nat String),
    impl.bidict.popitemOrderedBidict ({ data := item :: rest } : OrderedBidict Nat String) false =
      some ({ data := rest }, item)

/-- With `last = true`, `popitemOrderedBidict` removes and returns the final
    entry. -/
def spec_popitemOrderedBidict_last (impl : RepoImpl) : Prop :=
  ∀ (od : OrderedBidict Nat String) (item : Nat × String),
    od.data.getLast? = some item →
    impl.bidict.popitemOrderedBidict od true =
      some ({ data := od.data.take (od.data.length - 1) }, item)

/-- Moving a key that is not present is a no-op; the ordered bidict is returned
    unchanged. -/
def spec_moveToEnd_absent_noop (impl : RepoImpl) : Prop :=
  ∀ (od : OrderedBidict Nat String) (key : Nat) (last : Bool),
    key ∉ od.data.map Prod.fst →
    impl.bidict.moveToEndOrderedBidict od key last = od

/-- With `last = true`, an existing key is moved to the end of the list. -/
def spec_moveToEnd_last_appends (impl : RepoImpl) : Prop :=
  ∀ (od : OrderedBidict Nat String) (key : Nat),
    impl.bidict.moveToEndOrderedBidict od key true =
      match od.data.find? (fun (k, _) => k == key) with
      | none => od
      | some item =>
          { data := od.data.filter (fun (k, _) => !(k == key)) ++ [item] }

/-- With `last = false`, an existing key is moved to the front (beginning) of
    the list. -/
def spec_moveToEnd_first_prepends (impl : RepoImpl) : Prop :=
  ∀ (od : OrderedBidict Nat String) (key : Nat),
    impl.bidict.moveToEndOrderedBidict od key false =
      match od.data.find? (fun (k, _) => k == key) with
      | none => od
      | some item =>
          { data := item :: od.data.filter (fun (k, _) => !(k == key)) }

/-- `keysOrderedBidict` returns the first projection of `data`; it equals
    `od.data.map Prod.fst`. -/
def spec_keysOrderedBidict_first_proj (impl : RepoImpl) : Prop :=
  ∀ (od : OrderedBidict Nat String),
    impl.bidict.keysOrderedBidict od = od.data.map Prod.fst

/-- `itemsOrderedBidict` returns the underlying `data` list verbatim. -/
def spec_itemsOrderedBidict_data (impl : RepoImpl) : Prop :=
  ∀ (od : OrderedBidict Nat String),
    impl.bidict.itemsOrderedBidict od = od.data

/-- The key list from `keysOrderedBidict` equals the first projection of the
    item list from `itemsOrderedBidict`. Cross-API consistency invariant. -/
def spec_keys_eq_items_fst (impl : RepoImpl) : Prop :=
  ∀ (od : OrderedBidict Nat String),
    impl.bidict.keysOrderedBidict od =
      (impl.bidict.itemsOrderedBidict od).map Prod.fst

/-- Universal pair-swap: the items of `inverseOrderedBidict od` are the items
    of `od` with each `(k, v)` swapped to `(v, k)`. Generalises the concrete
    pin `spec_inverseOrderedBidict_swaps` over an arbitrary input. -/
def spec_inverseOrderedBidict_items_swap (impl : RepoImpl) : Prop :=
  ∀ (od : OrderedBidict Nat String),
    impl.bidict.itemsOrderedBidict (impl.bidict.inverseOrderedBidict od) =
      (impl.bidict.itemsOrderedBidict od).map (fun item => (item.2, item.1))

/-- Semantic guarantee for `popOrderedBidict`: when the operation succeeds, the
    returned value paired with the requested key is one of the items of the
    original ordered bidict, and the requested key is no longer among the keys
    of the residual ordered bidict. When the result is `none`, the key was not
    present in the original ordered bidict. -/
def spec_popOrderedBidict_returned_pair_membership (impl : RepoImpl) : Prop :=
  ∀ (od : OrderedBidict Nat String) (key : Nat),
    match impl.bidict.popOrderedBidict od key with
    | some (od', v) =>
        (key, v) ∈ impl.bidict.itemsOrderedBidict od ∧
        key ∉ impl.bidict.keysOrderedBidict od'
    | none => key ∉ impl.bidict.keysOrderedBidict od
