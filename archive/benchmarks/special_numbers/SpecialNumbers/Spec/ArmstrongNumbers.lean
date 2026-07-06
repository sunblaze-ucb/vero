import SpecialNumbers.Harness

/-!
# SpecialNumbers.Spec.ArmstrongNumbers

Specifications for Armstrong/Pluperfect/Narcissistic numbers.
Each `spec_*` is a property over an arbitrary `impl : RepoImpl`.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- The three Armstrong-style predicates are alternate names for the same classification. -/
def spec_armstrong_checkers_agree (impl : RepoImpl) : Prop :=
  ∀ n : Int, n > 0 →
    impl.specialNumbers.armstrong_number n = impl.specialNumbers.pluperfect_number n ∧
    impl.specialNumbers.armstrong_number n = impl.specialNumbers.narcissistic_number n
