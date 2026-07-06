import SpecialNumbers.Harness
import SpecialNumbers.Spec.Aux

/-!
# SpecialNumbers.Spec.GreatestCommonDivisor

Specifications for GCD algorithms.
Each `spec_*` is a property over an arbitrary `impl : RepoImpl`.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- Recursive and iterative Euclidean implementations are extensionally equal. -/
def spec_gcd_implementations_agree (impl : RepoImpl) : Prop :=
  ∀ a b : Int,
    impl.specialNumbers.greatest_common_divisor a b =
      impl.specialNumbers.gcd_by_iterative a b

/-- For nonzero input pairs, the reported GCD divides both arguments. -/
def spec_gcd_divides_inputs (impl : RepoImpl) : Prop :=
  ∀ a b : Int, a ≠ 0 ∨ b ≠ 0 →
    aux_divides (impl.specialNumbers.greatest_common_divisor a b) a ∧
    aux_divides (impl.specialNumbers.greatest_common_divisor a b) b
