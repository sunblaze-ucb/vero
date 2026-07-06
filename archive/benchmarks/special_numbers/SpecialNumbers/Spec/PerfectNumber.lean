import SpecialNumbers.Harness

/-!
# SpecialNumbers.Spec.PerfectNumber

Specifications for perfect numbers.
Each `spec_*` is a property over an arbitrary `impl : RepoImpl`.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- A number cannot be both perfect and abundant. -/
def spec_perfect_not_abundant (impl : RepoImpl) : Prop :=
  ∀ n : Int, impl.specialNumbers.perfect n = true →
    impl.specialNumbers.abundant n = false
