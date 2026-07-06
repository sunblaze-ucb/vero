import SpecialNumbers.Harness
import SpecialNumbers.Spec.Aux

/-!
# SpecialNumbers.Spec.WeirdNumber

Specifications for weird, abundant, and semi-perfect numbers.
Each `spec_*` is a property over an arbitrary `impl : RepoImpl`.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- Factor lists for positive inputs contain only positive divisors of the input. -/
def spec_factors_are_positive_divisors (impl : RepoImpl) : Prop :=
  ∀ n : Int, n > 0 →
    aux_allPositive (impl.specialNumbers.factors n) ∧
    ∀ d, d ∈ impl.specialNumbers.factors n → aux_divides d n

/-- Weird numbers are exactly abundant numbers that are not semiperfect. -/
def spec_weird_decomposes_into_abundant_not_semiperfect (impl : RepoImpl) : Prop :=
  ∀ n : Int,
    impl.specialNumbers.weird n = true ↔
      impl.specialNumbers.abundant n = true ∧
      impl.specialNumbers.semi_perfect n = false
