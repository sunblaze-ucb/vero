import SpecialNumbers.Harness

/-!
# SpecialNumbers.Spec.HexagonalNumber

Specifications for hexagonal numbers.
Each `spec_*` is a property over an arbitrary `impl : RepoImpl`.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- The n-th hexagonal number is the (2n-1)-th triangular number. -/
def spec_hexagonal_triangular_bridge (impl : RepoImpl) : Prop :=
  ∀ n : Int, n ≥ 1 →
    impl.specialNumbers.hexagonal n =
      impl.specialNumbers.triangular_number (2 * n - 1)
