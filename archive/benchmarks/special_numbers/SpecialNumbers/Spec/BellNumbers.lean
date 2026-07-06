import SpecialNumbers.Harness

/-!
# SpecialNumbers.Spec.BellNumbers

Specifications for Bell numbers.
Each `spec_*` is a property over an arbitrary `impl : RepoImpl`.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- `bell_numbers k` returns exactly the prefix `[B(0), ..., B(k)]`. -/
def spec_bell_length (impl : RepoImpl) : Prop :=
  ∀ k : Int, k ≥ 0 →
    (impl.specialNumbers.bell_numbers k).length = k.toNat + 1
