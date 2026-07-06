import SpecialNumbers.Harness

/-!
# SpecialNumbers.Spec.KrishnamurthyNumber

Specifications for Krishnamurthy (Strong) numbers and factorial.
Each `spec_*` is a property over an arbitrary `impl : RepoImpl`.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- Factorial satisfies the standard recurrence above the base cases. -/
def spec_factorial_recurrence (impl : RepoImpl) : Prop :=
  ∀ n : Int, n > 1 →
    impl.specialNumbers.factorial n =
      n * impl.specialNumbers.factorial (n - 1)

/-- On positive single digits, Krishnamurthy classification is exactly the factorial fixed-point test. -/
def spec_krishnamurthy_single_digit_factorial (impl : RepoImpl) : Prop :=
  ∀ d : Int, 1 ≤ d → d ≤ 9 →
    impl.specialNumbers.krishnamurthy d =
      (impl.specialNumbers.factorial d == d)
