import SpecialNumbers.Harness

/-!
# SpecialNumbers.Spec.PolygonalNumbers

Specifications for polygonal numbers.
Each `spec_*` is a property over an arbitrary `impl : RepoImpl`.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- Triangular and hexagonal APIs agree with the generic polygonal formula. -/
def spec_polygonal_specializations_agree (impl : RepoImpl) : Prop :=
  ∀ n : Int, 0 ≤ n →
    impl.specialNumbers.triangular_number n = impl.specialNumbers.polygonal_num n 3 ∧
    impl.specialNumbers.hexagonal n = impl.specialNumbers.polygonal_num n 6
