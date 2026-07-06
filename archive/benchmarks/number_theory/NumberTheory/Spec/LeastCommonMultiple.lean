import NumberTheory.Harness

/-!
# NumberTheory.Spec.LeastCommonMultiple

Specifications for least common multiple operations.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- lcm(0, b) = 0 and lcm(a, 0) = 0 for all integers. -/
def spec_lcm_fast_zero (impl : RepoImpl) : Prop :=
  (∀ b : Int, impl.numberTheory.least_common_multiple_fast 0 b = 0) ∧
  (∀ a : Int, impl.numberTheory.least_common_multiple_fast a 0 = 0)

/-- Pin least_common_multiple_fast at all test inputs including zero cases. -/
def spec_lcm_fast_concrete_pins (impl : RepoImpl) : Prop :=
  impl.numberTheory.least_common_multiple_fast 5   2   = 10   ∧
  impl.numberTheory.least_common_multiple_fast 12  76  = 228  ∧
  impl.numberTheory.least_common_multiple_fast 10  20  = 20   ∧
  impl.numberTheory.least_common_multiple_fast 13  15  = 195  ∧
  impl.numberTheory.least_common_multiple_fast 4   31  = 124  ∧
  impl.numberTheory.least_common_multiple_fast 10  42  = 210  ∧
  impl.numberTheory.least_common_multiple_fast 43  34  = 1462 ∧
  impl.numberTheory.least_common_multiple_fast 5   12  = 60   ∧
  impl.numberTheory.least_common_multiple_fast 12  25  = 300  ∧
  impl.numberTheory.least_common_multiple_fast 10  25  = 50   ∧
  impl.numberTheory.least_common_multiple_fast 6   9   = 18   ∧
  impl.numberTheory.least_common_multiple_fast 0   10  = 0    ∧
  impl.numberTheory.least_common_multiple_fast 10  0   = 0    ∧
  impl.numberTheory.least_common_multiple_fast 1   1   = 1    ∧
  impl.numberTheory.least_common_multiple_fast 1   100 = 100  ∧
  impl.numberTheory.least_common_multiple_fast 100 1   = 100

/-- Pin least_common_multiple_slow at the 14 positive test inputs (zero cases excluded). -/
def spec_lcm_slow_concrete_pins (impl : RepoImpl) : Prop :=
  impl.numberTheory.least_common_multiple_slow 5   2   = 10   ∧
  impl.numberTheory.least_common_multiple_slow 12  76  = 228  ∧
  impl.numberTheory.least_common_multiple_slow 10  20  = 20   ∧
  impl.numberTheory.least_common_multiple_slow 13  15  = 195  ∧
  impl.numberTheory.least_common_multiple_slow 4   31  = 124  ∧
  impl.numberTheory.least_common_multiple_slow 10  42  = 210  ∧
  impl.numberTheory.least_common_multiple_slow 43  34  = 1462 ∧
  impl.numberTheory.least_common_multiple_slow 5   12  = 60   ∧
  impl.numberTheory.least_common_multiple_slow 12  25  = 300  ∧
  impl.numberTheory.least_common_multiple_slow 10  25  = 50   ∧
  impl.numberTheory.least_common_multiple_slow 6   9   = 18   ∧
  impl.numberTheory.least_common_multiple_slow 1   1   = 1    ∧
  impl.numberTheory.least_common_multiple_slow 1   100 = 100  ∧
  impl.numberTheory.least_common_multiple_slow 100 1   = 100

/-- The slow and fast LCM implementations agree at all positive test inputs. -/
def spec_lcm_two_impls_agree_pos (impl : RepoImpl) : Prop :=
  impl.numberTheory.least_common_multiple_slow 5   2  = impl.numberTheory.least_common_multiple_fast 5   2  ∧
  impl.numberTheory.least_common_multiple_slow 12  76 = impl.numberTheory.least_common_multiple_fast 12  76 ∧
  impl.numberTheory.least_common_multiple_slow 10  20 = impl.numberTheory.least_common_multiple_fast 10  20 ∧
  impl.numberTheory.least_common_multiple_slow 13  15 = impl.numberTheory.least_common_multiple_fast 13  15 ∧
  impl.numberTheory.least_common_multiple_slow 4   31 = impl.numberTheory.least_common_multiple_fast 4   31 ∧
  impl.numberTheory.least_common_multiple_slow 43  34 = impl.numberTheory.least_common_multiple_fast 43  34 ∧
  impl.numberTheory.least_common_multiple_slow 5   12 = impl.numberTheory.least_common_multiple_fast 5   12 ∧
  impl.numberTheory.least_common_multiple_slow 6   9  = impl.numberTheory.least_common_multiple_fast 6   9  ∧
  impl.numberTheory.least_common_multiple_slow 1   1  = impl.numberTheory.least_common_multiple_fast 1   1

/-- The algebraic identity lcm(a,b) * gcd(a,b) = a * b holds at positive test inputs. -/
def spec_lcm_gcd_product (impl : RepoImpl) : Prop :=
  impl.numberTheory.least_common_multiple_fast 5   2  * impl.numberTheory.greatest_common_divisor 5   2  = 5   * 2  ∧
  impl.numberTheory.least_common_multiple_fast 12  76 * impl.numberTheory.greatest_common_divisor 12  76 = 12  * 76 ∧
  impl.numberTheory.least_common_multiple_fast 10  20 * impl.numberTheory.greatest_common_divisor 10  20 = 10  * 20 ∧
  impl.numberTheory.least_common_multiple_fast 13  15 * impl.numberTheory.greatest_common_divisor 13  15 = 13  * 15 ∧
  impl.numberTheory.least_common_multiple_fast 48  18 * impl.numberTheory.greatest_common_divisor 48  18 = 48  * 18 ∧
  impl.numberTheory.least_common_multiple_fast 6   9  * impl.numberTheory.greatest_common_divisor 6   9  = 6   * 9

/-- The LCM (fast) of two positive integers is divisible by both of them. -/
def spec_lcm_is_common_multiple (impl : RepoImpl) : Prop :=
  ∀ (a b : Int), a > 0 → b > 0 →
    let l := impl.numberTheory.least_common_multiple_fast a b
    l % a = 0 ∧ l % b = 0

/-- The fast LCM is the least positive common multiple of two positive integers. -/
def spec_lcm_is_least_common_multiple (impl : RepoImpl) : Prop :=
  ∀ (a b m : Int), a > 0 → b > 0 → m > 0 →
    m % a = 0 → m % b = 0 →
      impl.numberTheory.least_common_multiple_fast a b ≤ m

/-- The slow (iterative search) and fast (GCD-based) LCM implementations agree at positive inputs. -/
def spec_lcm_implementations_agree (impl : RepoImpl) : Prop :=
  ∀ (a b : Int), a > 0 → b > 0 →
    impl.numberTheory.least_common_multiple_slow a b =
    impl.numberTheory.least_common_multiple_fast a b

/-- For positive integers, gcd(a, b) * lcm(a, b) = a * b. -/
def spec_gcd_lcm_product_identity (impl : RepoImpl) : Prop :=
  ∀ (a b : Int), a > 0 → b > 0 →
    impl.numberTheory.greatest_common_divisor a b *
      impl.numberTheory.least_common_multiple_fast a b = a * b
