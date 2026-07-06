import SpecialNumbers.Harness

/-!
# SpecialNumbers.Spec.PronicNumber

Specifications for pronic numbers.
Each `spec_*` is a property over an arbitrary `impl : RepoImpl`.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- Every constructive pronic value `m * (m + 1)` is accepted by the checker. -/
def spec_pronic_witness (impl : RepoImpl) : Prop :=
  ∀ m : Int, m ≥ 0 →
    impl.specialNumbers.is_pronic (m * (m + 1)) = true
