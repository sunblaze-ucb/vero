import Bidict.Harness

/-!
# Bidict.Spec.Iter

Specifications for the iteration utilities (`iteritems`, `inverted`).
Each `spec_*` is a property over an arbitrary `impl : RepoImpl`.

DO NOT MODIFY — frozen curator-given content.
-/

/-- `iteritems` on a `HashMap` (i.e. `List (KT × VT)`) returns the list
    unchanged; it is the identity function. -/
def spec_iteritems_identity (impl : RepoImpl) : Prop :=
  ∀ (hm : HashMap Nat String),
    impl.bidict.iteritems hm = hm

/-- `inverted` maps each `(k, v)` to `(v, k)`. -/
def spec_inverted_swaps (impl : RepoImpl) : Prop :=
  ∀ (hm : HashMap Nat String),
    impl.bidict.inverted hm = hm.map (fun item => (item.2, item.1))

/-- Applying `inverted` twice recovers the original list, which equals
    `iteritems` of that list (since `iteritems` is identity).
    Round-trip invariant linking the two Iter APIs. -/
def spec_inverted_involution_via_iteritems (impl : RepoImpl) : Prop :=
  ∀ (hm : HashMap Nat String),
    impl.bidict.inverted (impl.bidict.inverted hm) = impl.bidict.iteritems hm

/-- Universal pair-swap: `inverted hm` is `iteritems hm` with each `(k, v)`
    swapped to `(v, k)`. Relates the two Iter APIs by a single map equation
    rather than the involution round-trip. -/
def spec_inverted_eq_iteritems_swap (impl : RepoImpl) : Prop :=
  ∀ (hm : HashMap Nat String),
    impl.bidict.inverted hm =
      (impl.bidict.iteritems hm).map (fun item => (item.2, item.1))
