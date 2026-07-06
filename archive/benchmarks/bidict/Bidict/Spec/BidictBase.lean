import Bidict.Harness

/-!
# Bidict.Spec.BidictBase

Specifications for the core `BidictBase` operations (inverse, inv, copy,
union, runion, length, iter, getitem). Each `spec_*` is a property over an
arbitrary `impl : RepoImpl`.

DO NOT MODIFY — frozen curator-given content.
-/

/-- Reference model for association-list lookup: return the first matching key. -/
def spec_helper_getitemModel (m : BidictBase Nat String) (key : Nat) : Option String :=
  match m with
  | [] => none
  | (k, v) :: rest =>
      if k == key then some v else spec_helper_getitemModel rest key

/-- `inverse` swaps every pair in the input list. -/
def spec_inverse_swaps_pairs (impl : RepoImpl) : Prop :=
  ∀ (m : BidictBase Nat String),
    impl.bidict.inverse m = m.map (fun item => (item.2, item.1))

/-- `inverse` swaps every pair for every bidict, preserving order. -/
def spec_inverse_swaps_all_pairs (impl : RepoImpl) : Prop :=
  ∀ (m : BidictBase Nat String),
    impl.bidict.inverse m = m.map (fun item => (item.2, item.1))

/-- Applying `inverse` twice is the identity on any `BidictBase Nat String`. -/
def spec_inverse_involution (impl : RepoImpl) : Prop :=
  ∀ (m : BidictBase Nat String),
    impl.bidict.inverse (impl.bidict.inverse m) = m

/-- `inv` is an alias for `inverse`; they produce identical results. -/
def spec_inv_eq_inverse (impl : RepoImpl) : Prop :=
  ∀ (m : BidictBase Nat String),
    impl.bidict.inv m = impl.bidict.inverse m

/-- `length` agrees with the underlying association-list length. -/
def spec_length_eq_listLength (impl : RepoImpl) : Prop :=
  ∀ (m : BidictBase Nat String),
    impl.bidict.length m = m.length

/-- Inverting a bidict does not change its length. -/
def spec_length_inverse_symmetry (impl : RepoImpl) : Prop :=
  ∀ (m : BidictBase Nat String),
    impl.bidict.length (impl.bidict.inverse m) = impl.bidict.length m

/-- `copy` is the identity function on `BidictBase`. -/
def spec_copy_identity (impl : RepoImpl) : Prop :=
  ∀ (m : BidictBase Nat String),
    impl.bidict.copy m = m

/-- `union m []` is `m`: appending an empty second bidict changes nothing. -/
def spec_union_self_empty (impl : RepoImpl) : Prop :=
  ∀ (m : BidictBase Nat String),
    impl.bidict.union m [] = m

/-- `union [] m` is `m`: every entry of `m` passes the key-conflict filter. -/
def spec_union_empty_self (impl : RepoImpl) : Prop :=
  ∀ (m : BidictBase Nat String),
    impl.bidict.union [] m = m

/-- `runion m []` is `m`: with an empty right argument there are no overrides. -/
def spec_runion_self_empty (impl : RepoImpl) : Prop :=
  ∀ (m : BidictBase Nat String),
    impl.bidict.runion m [] = m

/-- `runion` updates self entries from the right argument and appends new keys. -/
def spec_runion_overrides (impl : RepoImpl) : Prop :=
  ∀ (self other : BidictBase Nat String),
    impl.bidict.runion self other =
      (self.map (fun (k, v) =>
        match other.find? (fun (k', _) => k' == k) with
        | some (_, v') => (k, v')
        | none => (k, v))) ++
      other.filter (fun (k, _) => !self.any (fun (k', _) => k' == k))

/-- `iter` returns the first projection (key) of every pair in insertion order. -/
def spec_iter_keys (impl : RepoImpl) : Prop :=
  ∀ (m : BidictBase Nat String),
    impl.bidict.iter m = m.map Prod.fst

/-- `getitem` is association-list lookup by key. -/
def spec_getitem_consistent_with_membership (impl : RepoImpl) : Prop :=
  ∀ (m : BidictBase Nat String) (key : Nat),
    impl.bidict.getitem m key =
      (m.find? (fun (k, _) => k == key)).map Prod.snd

/-- `getitem` is exactly first-match association-list lookup. -/
def spec_getitem_matches_first_key (impl : RepoImpl) : Prop :=
  ∀ (m : BidictBase Nat String) (key : Nat),
    impl.bidict.getitem m key = spec_helper_getitemModel m key

/-- `length` agrees with the length of the iterated key list, for every input.
    Universal cross-API consistency: the count returned by `length` is the same
    as the number of keys yielded by `iter`. -/
def spec_length_eq_iter_length (impl : RepoImpl) : Prop :=
  ∀ (m : BidictBase Nat String),
    impl.bidict.length m = (impl.bidict.iter m).length
