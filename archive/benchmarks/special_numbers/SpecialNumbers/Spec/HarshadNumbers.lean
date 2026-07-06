import SpecialNumbers.Harness

/-!
# SpecialNumbers.Spec.HarshadNumbers

Specifications for Harshad numbers and base conversion.
Each `spec_*` is a property over an arbitrary `impl : RepoImpl`.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- Every generated Harshad string names a checked Harshad number below the requested limit. -/
def spec_harshad_generator_checker_agreement (impl : RepoImpl) : Prop :=
  ∀ limit base : Int, 0 < limit → 2 ≤ base → base ≤ 36 →
    ∀ s, s ∈ impl.specialNumbers.harshad_numbers_in_base limit base →
      ∃ n : Int, 0 < n ∧ n < limit ∧
        impl.specialNumbers.int_to_base n base = s ∧
        impl.specialNumbers.is_harshad_number_in_base n base = true

/-- Accepted positive Harshad inputs have a nonzero digit-sum representation. -/
def spec_harshad_digit_sum_nonzero (impl : RepoImpl) : Prop :=
  ∀ n base : Int, 0 < n → 2 ≤ base → base ≤ 36 →
    impl.specialNumbers.is_harshad_number_in_base n base = true →
    impl.specialNumbers.sum_of_digits n base ≠ "0"
