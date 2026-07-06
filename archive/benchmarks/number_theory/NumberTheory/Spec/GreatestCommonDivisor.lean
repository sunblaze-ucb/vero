import NumberTheory.Harness

/-!
# NumberTheory.Spec.GreatestCommonDivisor

Specifications for greatest common divisor operations.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- When the first argument is 0, the GCD of (0, b) is the absolute value of b. -/
def spec_gcd_zero_left (impl : RepoImpl) : Prop :=
  ∀ b : Int, impl.numberTheory.greatest_common_divisor 0 b = (b.natAbs : Int)

/-- When the second argument is 0, gcd(a, 0) = |a|. -/
def spec_gcd_zero_right (impl : RepoImpl) : Prop :=
  ∀ a : Int, impl.numberTheory.greatest_common_divisor a 0 = (a.natAbs : Int)

/-- The GCD is always non-negative for all integer inputs. -/
def spec_gcd_nonneg (impl : RepoImpl) : Prop :=
  ∀ a b : Int, 0 ≤ impl.numberTheory.greatest_common_divisor a b

/-- Pin the output of greatest_common_divisor to expected values at all test inputs. -/
def spec_gcd_concrete_pins (impl : RepoImpl) : Prop :=
  impl.numberTheory.greatest_common_divisor 24 40     = 8  ∧
  impl.numberTheory.greatest_common_divisor 1  1      = 1  ∧
  impl.numberTheory.greatest_common_divisor 1  800    = 1  ∧
  impl.numberTheory.greatest_common_divisor 11 37     = 1  ∧
  impl.numberTheory.greatest_common_divisor 16 4      = 4  ∧
  impl.numberTheory.greatest_common_divisor (-3) 9    = 3  ∧
  impl.numberTheory.greatest_common_divisor 9 (-3)    = 3  ∧
  impl.numberTheory.greatest_common_divisor 3 (-9)    = 3  ∧
  impl.numberTheory.greatest_common_divisor (-3) (-9) = 3  ∧
  impl.numberTheory.greatest_common_divisor 0 0       = 0  ∧
  impl.numberTheory.greatest_common_divisor 0 5       = 5  ∧
  impl.numberTheory.greatest_common_divisor 5 0       = 5  ∧
  impl.numberTheory.greatest_common_divisor 48 18     = 6  ∧
  impl.numberTheory.greatest_common_divisor 100 75    = 25

/-- Pin the output of gcd_by_iterative to expected values at all test inputs. -/
def spec_gcd_iterative_concrete_pins (impl : RepoImpl) : Prop :=
  impl.numberTheory.gcd_by_iterative 24 40     = 8  ∧
  impl.numberTheory.gcd_by_iterative (-3) (-9) = 3  ∧
  impl.numberTheory.gcd_by_iterative 3 (-9)    = 3  ∧
  impl.numberTheory.gcd_by_iterative 1 (-800)  = 1  ∧
  impl.numberTheory.gcd_by_iterative 11 37     = 1  ∧
  impl.numberTheory.gcd_by_iterative 0 0       = 0  ∧
  impl.numberTheory.gcd_by_iterative 0 5       = 5  ∧
  impl.numberTheory.gcd_by_iterative 5 0       = 5  ∧
  impl.numberTheory.gcd_by_iterative 48 18     = 6  ∧
  impl.numberTheory.gcd_by_iterative 100 75    = 25

/-- The recursive and iterative GCD implementations agree on all integer inputs. -/
def spec_gcd_two_impls_agree (impl : RepoImpl) : Prop :=
  ∀ a b : Int,
    impl.numberTheory.greatest_common_divisor a b =
    impl.numberTheory.gcd_by_iterative a b

/-- The GCD of two positive integers divides both of them. -/
def spec_gcd_divides_both (impl : RepoImpl) : Prop :=
  ∀ (a b : Int), a > 0 → b > 0 →
    let g := impl.numberTheory.greatest_common_divisor a b
    a % g = 0 ∧ b % g = 0

/-- The GCD is the greatest positive common divisor of two positive integers. -/
def spec_gcd_greatest_common_divisor (impl : RepoImpl) : Prop :=
  ∀ (a b d : Int), a > 0 → b > 0 → d > 0 →
    a % d = 0 → b % d = 0 →
      d ≤ impl.numberTheory.greatest_common_divisor a b

/-- GCD is symmetric: swapping the arguments does not change the result. -/
def spec_gcd_symmetry (impl : RepoImpl) : Prop :=
  ∀ (a b : Int),
    impl.numberTheory.greatest_common_divisor a b =
    impl.numberTheory.greatest_common_divisor b a

/-- GCD ignores signs: gcd(a, b) = gcd(|a|, |b|). -/
def spec_gcd_sign_invariance (impl : RepoImpl) : Prop :=
  ∀ (a b : Int),
    impl.numberTheory.greatest_common_divisor a b =
    impl.numberTheory.greatest_common_divisor (Int.natAbs a) (Int.natAbs b)
