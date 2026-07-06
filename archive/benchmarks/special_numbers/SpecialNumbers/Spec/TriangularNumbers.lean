import SpecialNumbers.Harness

/-!
# SpecialNumbers.Spec.TriangularNumbers

Specifications for triangular numbers.
Each `spec_*` is a property over an arbitrary `impl : RepoImpl`.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- Algebraic recurrence: T(n) = T(n-1) + n for every positive position. -/
def spec_triangular_recurrence (impl : RepoImpl) : Prop :=
  ∀ n : Int, n > 0 →
    impl.specialNumbers.triangular_number n =
      impl.specialNumbers.triangular_number (n - 1) + n
