import VerifiedBitmasks.Harness

/-!
# VerifiedBitmasks.Spec.BitmaskIF

Specifications for the bitmask interface (`BitmaskIF`). Each `spec_*` is a
mathematical property over an arbitrary `impl : RepoImpl` that must hold for
any correct implementation of the fourteen bitmask API functions.

Translated from the `lemma_bitmask_split_concat` ensures clause in
`src/BitMask/Spec/BitmaskIF.s.dfy`.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- Splitting the concatenation of `A` and `B` at the length of `A` recovers `A` and `B`. -/
def spec_bIF_split_concat (impl : RepoImpl) : Prop :=
  ∀ (A B : T),
    impl.verifiedBitmasks.bIF_split (impl.verifiedBitmasks.bIF_concat A B)
      (impl.verifiedBitmasks.bIF_nbits A) = (A, B)
