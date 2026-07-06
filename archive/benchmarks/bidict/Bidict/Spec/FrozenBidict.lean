import Bidict.Harness

/-!
# Bidict.Spec.FrozenBidict

Specifications for the frozen bidict hash utility (`frozenBidictHash`).
Each `spec_*` is a property over an arbitrary `impl : RepoImpl`.

DO NOT MODIFY — frozen curator-given content.
-/

/-- The hash of an empty bidict is zero, because the fold over an empty list
    returns the initial accumulator. -/
def spec_frozenBidictHash_empty (impl : RepoImpl) : Prop :=
  impl.bidict.frozenBidictHash ([] : BidictBase Nat String) = 0

/-- The hash is order-independent over any permutation of the entry list. -/
def spec_frozenBidictHash_orderIndependent (impl : RepoImpl) : Prop :=
  ∀ (m1 m2 : BidictBase Nat String),
    m1.Perm m2 →
    impl.bidict.frozenBidictHash m1 = impl.bidict.frozenBidictHash m2

/-- Universal order-independence (permutation invariance): any two bidicts
    whose underlying entry lists are permutations of each other hash to the
    same value. Generalises `spec_frozenBidictHash_orderIndependent` from a
    fixed two-entry pin to the `List.Perm` relation. -/
def spec_frozenBidictHash_perm_invariant (impl : RepoImpl) : Prop :=
  ∀ (m1 m2 : BidictBase Nat String),
    m1.Perm m2 →
    impl.bidict.frozenBidictHash m1 = impl.bidict.frozenBidictHash m2
