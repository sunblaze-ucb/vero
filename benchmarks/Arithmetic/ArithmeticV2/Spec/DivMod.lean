import ArithmeticV2.Impl.DivMod
import ArithmeticV2.Harness

/-!
# ArithmeticV2.Spec.DivMod

Specifications for division and modulo helper properties. Each `spec_*` is a
property over an arbitrary `impl : RepoImpl`; this module has no scored APIs, so
the properties are stated over the frozen helper vocabulary.

DO NOT MODIFY -- this file is frozen curator-given content.
-/

open ArithmeticV2

/-- Division using `/` is equivalent to the recursive division helper. -/
def spec_lemma_div_is_div_recursive (_impl : RepoImpl) : Prop :=
  ∀ (x : Int) (d : Int), 0 < d → div_recursive x d = x / d

/-- The quotient of a nonzero integer divided by itself is 1. -/
def spec_lemma_div_by_self (_impl : RepoImpl) : Prop :=
  ∀ (d : Int), d ≠ 0 → d / d = 1

/-- Zero divided by a nonzero integer is zero. -/
def spec_lemma_div_of0 (_impl : RepoImpl) : Prop :=
  ∀ (d : Int), d ≠ 0 → (0 : Int) / d = 0

/-- Dividing a nonnegative integer by a positive integer is nonnegative. -/
def spec_lemma_div_basics_4 (_impl : RepoImpl) : Prop :=
  ∀ (x : Int) (y : Int), x ≥ 0 ∧ y > 0 → x / y ≥ 0

/-- If a nonnegative dividend has quotient zero under a positive divisor, it is smaller than the divisor. -/
def spec_lemma_small_div_converse (_impl : RepoImpl) : Prop :=
  ∀ (x : Int) (d : Int), 0 ≤ x ∧ 0 < d ∧ x / d = 0 → x < d

/-- Division by a divisor greater than one strictly decreases a positive integer. -/
def spec_lemma_div_is_strictly_smaller (_impl : RepoImpl) : Prop :=
  ∀ (x : Int) (d : Int), 0 < x ∧ 1 < d → x / d < x

/-- Dividing a nonnegative integer by a positive integer gives a nonnegative quotient. -/
def spec_lemma_div_pos_is_pos (_impl : RepoImpl) : Prop :=
  ∀ (x : Int) (d : Int), 0 ≤ x ∧ 0 < d → 0 ≤ x / d

/-- Adding the divisor before division increases the quotient by one. -/
def spec_lemma_div_plus_one (_impl : RepoImpl) : Prop :=
  ∀ (x : Int) (d : Int), 0 < d → 1 + x / d = (d + x) / d

/-- Subtracting the divisor before division decreases the quotient by one. -/
def spec_lemma_div_minus_one (_impl : RepoImpl) : Prop :=
  ∀ (x : Int) (d : Int), 0 < d → -1 + x / d = (-d + x) / d

/-- Values in the half-open range `[0, d)` divide by `d` to quotient zero. -/
def spec_lemma_basic_div_specific_divisor (_impl : RepoImpl) : Prop :=
  ∀ (d : Int), 0 < d → ∀ (x : Int), 0 ≤ x ∧ x < d → x / d = 0

/-- Order is preserved when dividing by a common positive divisor. -/
def spec_lemma_div_is_ordered (_impl : RepoImpl) : Prop :=
  ∀ (x : Int) (y : Int) (z : Int), x ≤ y ∧ 0 < z → x / z ≤ y / z

/-- Dividing a positive integer by two or more strictly decreases it. -/
def spec_lemma_div_decreases (_impl : RepoImpl) : Prop :=
  ∀ (x : Int) (d : Int), 0 < x ∧ 1 < d → x / d < x

/-- Dividing a nonnegative integer by a positive integer is nonincreasing. -/
def spec_lemma_div_nonincreasing (_impl : RepoImpl) : Prop :=
  ∀ (x : Int) (d : Int), 0 ≤ x ∧ 0 < d → x / d ≤ x

/-- A natural number smaller than a positive modulus is its own remainder. -/
def spec_lemma_small_mod (_impl : RepoImpl) : Prop :=
  ∀ (x : Nat) (m : Nat), x < m ∧ 0 < m → x % m = x

/-- The lower multiple of the divisor is strictly above `x - d`. -/
def spec_lemma_remainder_upper (_impl : RepoImpl) : Prop :=
  ∀ (x : Int) (d : Int), 0 ≤ x ∧ 0 < d → x - d < x / d * d

/-- The lower multiple of the divisor is at most the dividend. -/
def spec_lemma_remainder_lower (_impl : RepoImpl) : Prop :=
  ∀ (x : Int) (d : Int), 0 ≤ x ∧ 0 < d → x ≥ x / d * d

/-- The division remainder is in the half-open range `[0, d)`. -/
def spec_lemma_remainder (_impl : RepoImpl) : Prop :=
  ∀ (x : Int) (d : Int),
    0 ≤ x ∧ 0 < d → 0 ≤ x - (x / d * d) ∧ x - (x / d * d) < d

/-- Fundamental theorem of division and modulo. -/
def spec_lemma_fundamental_div_mod (_impl : RepoImpl) : Prop :=
  ∀ (x : Int) (d : Int), d ≠ 0 → x = d * (x / d) + x % d

/-- Values in the same divisor bucket have indistinguishable quotients. -/
def spec_lemma_indistinguishable_quotients (_impl : RepoImpl) : Prop :=
  ∀ (a : Int) (b : Int) (d : Int),
    0 < d ∧ a - a % d ≤ b ∧ b < a + d - a % d → a / d = b / d

/-- Rounding down across a zero-remainder base preserves the base multiple. -/
def spec_lemma_round_down (_impl : RepoImpl) : Prop :=
  ∀ (a : Int) (r : Int) (d : Int),
    0 < d ∧ a % d = 0 ∧ (0 ≤ r ∧ r < d) → a = d * ((a + r) / d)

/-- Modulo using `%` is equivalent to the recursive modulo helper. -/
def spec_lemma_mod_is_mod_recursive (_impl : RepoImpl) : Prop :=
  ∀ (x : Int) (m : Int), m > 0 → mod_recursive x m = x % m

/-- A positive integer modulo itself is zero. -/
def spec_lemma_mod_self_0 (_impl : RepoImpl) : Prop :=
  ∀ (m : Int), m > 0 → m % m = 0

/-- Taking modulo twice is the same as taking modulo once. -/
def spec_lemma_mod_twice (_impl : RepoImpl) : Prop :=
  ∀ (x : Int) (m : Int), m > 0 → (x % m) % m = x % m

/-- The integer remainder is nonnegative and smaller than the positive divisor. -/
def spec_lemma_mod_division_less_than_divisor (_impl : RepoImpl) : Prop :=
  ∀ (x : Int) (m : Int), m > 0 → 0 ≤ x % m ∧ x % m < m

/-- A natural-number remainder is at most the dividend. -/
def spec_lemma_mod_decreases (_impl : RepoImpl) : Prop :=
  ∀ (x : Nat) (m : Nat), 0 < m → x % m ≤ x

/-- A multiple of a positive divisor has remainder zero. -/
def spec_lemma_mod_multiples_basic (_impl : RepoImpl) : Prop :=
  ∀ (x : Int) (m : Int), m > 0 → (x * m) % m = 0

/-- Adding the divisor does not change the remainder. -/
def spec_lemma_mod_add_multiples_vanish (_impl : RepoImpl) : Prop :=
  ∀ (b : Int) (m : Int), 0 < m → (m + b) % m = b % m

/-- Subtracting the divisor does not change the remainder. -/
def spec_lemma_mod_sub_multiples_vanish (_impl : RepoImpl) : Prop :=
  ∀ (b : Int) (m : Int), 0 < m → (-m + b) % m = b % m

/-- Adding any multiple of the divisor does not change the remainder. -/
def spec_lemma_mod_multiples_vanish (_impl : RepoImpl) : Prop :=
  ∀ (a : Int) (b : Int) (m : Int), 0 < m → (m * a + b) % m = b % m

/-- Modulo distributes over subtraction in the source's bounded natural case. -/
def spec_lemma_mod_subtraction (_impl : RepoImpl) : Prop :=
  ∀ (x : Nat) (s : Nat) (d : Nat),
    0 < d ∧ s ≤ x % d →
      ((x % d : Nat) : Int) - ((s % d : Nat) : Int) = (((x - s) % d : Nat) : Int)

/-- Modulo distributes over addition after normalizing the sum of remainders. -/
def spec_lemma_add_mod_noop (_impl : RepoImpl) : Prop :=
  ∀ (x : Int) (y : Int) (m : Int), 0 < m → ((x % m) + (y % m)) % m = (x + y) % m

/-- Replacing the right addend with its remainder does not change the sum remainder. -/
def spec_lemma_add_mod_noop_right (_impl : RepoImpl) : Prop :=
  ∀ (x : Int) (y : Int) (m : Int), 0 < m → (x + (y % m)) % m = (x + y) % m

/-- Modulo distributes over subtraction after normalizing the difference of remainders. -/
def spec_lemma_sub_mod_noop (_impl : RepoImpl) : Prop :=
  ∀ (x : Int) (y : Int) (m : Int), 0 < m → ((x % m) - (y % m)) % m = (x - y) % m

/-- Replacing the right subtrahend with its remainder does not change the difference remainder. -/
def spec_lemma_sub_mod_noop_right (_impl : RepoImpl) : Prop :=
  ∀ (x : Int) (y : Int) (m : Int), 0 < m → (x - (y % m)) % m = (x - y) % m

/-- Sum of remainders has the source carry decomposition. -/
def spec_lemma_mod_adds (_impl : RepoImpl) : Prop :=
  ∀ (a : Int) (b : Int) (d : Int),
    0 < d →
      a % d + b % d = (a + b) % d + d * ((a % d + b % d) / d) ∧
      ((a % d + b % d) < d → a % d + b % d = (a + b) % d)

/-- Multiplication by `1 - d` preserves the remainder modulo positive `d`. -/
def spec_lemma_mod_neg_neg (_impl : RepoImpl) : Prop :=
  ∀ (x : Int) (d : Int), 0 < d → x % d = (x * (1 - d)) % d

/-- The remainder of a nonnegative integer by a positive divisor is in range. -/
def spec_lemma_mod_pos_bound (_impl : RepoImpl) : Prop :=
  ∀ (x : Int) (m : Int), 0 ≤ x ∧ 0 < m → 0 ≤ x % m ∧ x % m < m

/-- The remainder of any integer by a positive divisor is in range. -/
def spec_lemma_mod_bound (_impl : RepoImpl) : Prop :=
  ∀ (x : Int) (m : Int), 0 < m → 0 ≤ x % m ∧ x % m < m

/-- Replacing the left factor with its remainder preserves the product remainder. -/
def spec_lemma_mul_mod_noop_left (_impl : RepoImpl) : Prop :=
  ∀ (x : Int) (y : Int) (m : Int), 0 < m → ((x % m) * y) % m = (x * y) % m

/-- Replacing the right factor with its remainder preserves the product remainder. -/
def spec_lemma_mul_mod_noop_right (_impl : RepoImpl) : Prop :=
  ∀ (x : Int) (y : Int) (m : Int), 0 < m → (x * (y % m)) % m = (x * y) % m

/-- Congruence modulo `m` is equivalent to the difference having zero remainder. -/
def spec_lemma_mod_equivalence (_impl : RepoImpl) : Prop :=
  ∀ (x : Int) (y : Int) (m : Int), 0 < m → (x % m = y % m ↔ (x - y) % m = 0)

/-- Basic division facts for zero, one, and self divisors. -/
def spec_lemma_div_basics (_impl : RepoImpl) : Prop :=
  ∀ (x : Int),
    (x ≠ 0 → (0 : Int) / x = 0) ∧
    x / 1 = x ∧
    (x ≠ 0 → x / x = 1)

/-- Division of a positive integer by a positive integer no greater than it is positive. -/
def spec_lemma_div_non_zero (_impl : RepoImpl) : Prop :=
  ∀ (x : Int) (d : Int), x ≥ d ∧ d > 0 → x / d > 0

/-- For a fixed nonnegative numerator, division is ordered contravariantly by denominator. -/
def spec_lemma_div_is_ordered_by_denominator (_impl : RepoImpl) : Prop :=
  ∀ (x : Int) (y : Int) (z : Int), 0 ≤ x ∧ (1 ≤ y ∧ y ≤ z) → x / y ≥ x / z

/-- Dividing sums exposes the carry in the sum of remainders. -/
def spec_lemma_dividing_sums (_impl : RepoImpl) : Prop :=
  ∀ (a : Int) (b : Int) (d : Int) (r : Int),
    0 < d ∧ r = a % d + b % d - (a + b) % d →
      d * ((a + b) / d) - r = d * (a / d) + d * (b / d)

/-- A nonnegative integer smaller than the divisor has quotient zero. -/
def spec_lemma_basic_div (_impl : RepoImpl) : Prop :=
  ∀ (x : Int) (d : Int), 0 ≤ x ∧ x < d → x / d = 0

/-- A smaller dividend has smaller quotient than a positive multiple of the divisor. -/
def spec_lemma_div_by_multiple_is_strongly_ordered (_impl : RepoImpl) : Prop :=
  ∀ (x : Int) (y : Int) (m : Int) (z : Int),
    x < y ∧ y = m * z ∧ 0 < z → x / z < y / z

/-- Bound on the truncated part modulo `b * c`. -/
def spec_lemma_part_bound1 (_impl : RepoImpl) : Prop :=
  ∀ (a : Int) (b : Int) (c : Int),
    0 ≤ a ∧ 0 < b ∧ 0 < c → 0 < b * c ∧ (b * (a / b) % (b * c)) ≤ b * (c - 1)

/-- A positive natural number with zero remainder is at least the positive modulus. -/
def spec_lemma_mod_is_zero (_impl : RepoImpl) : Prop :=
  ∀ (x : Nat) (m : Nat), x > 0 ∧ m > 0 ∧ x % m = 0 → x ≥ m

/-- Converse of fundamental div/mod for the remainder. -/
def spec_lemma_fundamental_div_mod_converse_mod (_impl : RepoImpl) : Prop :=
  ∀ (x : Int) (d : Int) (q : Int) (r : Int),
    d ≠ 0 ∧ (0 ≤ r ∧ r < d) ∧ x = q * d + r → r = x % d

/-- Converse of fundamental div/mod for the quotient. -/
def spec_lemma_fundamental_div_mod_converse_div (_impl : RepoImpl) : Prop :=
  ∀ (x : Int) (d : Int) (q : Int) (r : Int),
    d ≠ 0 ∧ (0 ≤ r ∧ r < d) ∧ x = q * d + r → q = x / d

/-- Product modulo normalization facts for left, right, and both factors. -/
def spec_lemma_mul_mod_noop_general (_impl : RepoImpl) : Prop :=
  ∀ (x : Int) (y : Int) (m : Int),
    0 < m →
      ((x % m) * y) % m = (x * y) % m ∧
      (x * (y % m)) % m = (x * y) % m ∧
      ((x % m) * (y % m)) % m = (x * y) % m

/-- Modulo equivalence is preserved by multiplying both sides by the same factor. -/
def spec_lemma_mod_mul_equivalent (_impl : RepoImpl) : Prop :=
  ∀ (x : Int) (y : Int) (z : Int) (m : Int),
    m > 0 ∧ is_mod_equivalent x y m → is_mod_equivalent (x * z) (y * z) m

/-- Multiplying the divisor by a positive factor cannot decrease the remainder. -/
def spec_lemma_mod_ordering (_impl : RepoImpl) : Prop :=
  ∀ (x : Int) (k : Int) (d : Int),
    1 < d ∧ 0 < k → 0 < d * k ∧ x % d ≤ x % (d * k)

/-- Bound on `(x % y) % (y * z)`. -/
def spec_lemma_part_bound2 (_impl : RepoImpl) : Prop :=
  ∀ (x : Int) (y : Int) (z : Int),
    0 ≤ x ∧ 0 < y ∧ 0 < z → y * z > 0 ∧ (x % y) % (y * z) < y

/-- Zero divided by a nonzero integer is zero. -/
def spec_lemma_div_basics_1 (_impl : RepoImpl) : Prop :=
  ∀ (x : Int), x ≠ 0 → 0 / x = 0

/-- Any integer divided by one is itself. -/
def spec_lemma_div_basics_2 (_impl : RepoImpl) : Prop :=
  ∀ (x : Int), x / 1 = x

/-- Any nonzero integer divided by itself is one. -/
def spec_lemma_div_basics_3 (_impl : RepoImpl) : Prop :=
  ∀ (x : Int), x ≠ 0 → x / x = 1

/-- Dividing a nonnegative integer by a positive integer yields at most the dividend. -/
def spec_lemma_div_basics_5 (_impl : RepoImpl) : Prop :=
  ∀ (x : Int) (y : Int), x ≥ 0 ∧ y > 0 → x / y ≤ x

/-- If `0 <= b < d`, then `(d * x + b) / d = x`. -/
def spec_lemma_div_multiples_vanish_fancy (_impl : RepoImpl) : Prop :=
  ∀ (x : Int) (b : Int) (d : Int), 0 < d ∧ (0 ≤ b ∧ b < d) → (d * x + b) / d = x

/-- Converse of the fundamental div/mod theorem for quotient and remainder. -/
def spec_lemma_fundamental_div_mod_converse (_impl : RepoImpl) : Prop :=
  ∀ (x : Int) (d : Int) (q : Int) (r : Int),
    d ≠ 0 ∧ (0 ≤ r ∧ r < d) ∧ x = q * d + r → r = x % d ∧ q = x / d

/-- Product modulo normalization for both factors. -/
def spec_lemma_mul_mod_noop (_impl : RepoImpl) : Prop :=
  ∀ (x : Int) (y : Int) (m : Int), 0 < m → ((x % m) * (y % m)) % m = (x * y) % m

/-- Multiples of a positive divisor divide back to the multiplier. -/
def spec_lemma_div_multiples_vanish (_impl : RepoImpl) : Prop :=
  ∀ (x : Int) (d : Int), 0 < d → (d * x) / d = x

/-- Hoisting an integer over a positive natural denominator. -/
def spec_lemma_hoist_over_denominator (_impl : RepoImpl) : Prop :=
  ∀ (x : Int) (j : Int) (d : Nat),
    0 < d → x / (d : Int) + j = (x + j * (d : Int)) / (d : Int)

/-- Modulo by `a * b`, then by `a`, is equivalent to modulo by `a`. -/
def spec_lemma_mod_mod (_impl : RepoImpl) : Prop :=
  ∀ (x : Int) (a : Int) (b : Int),
    0 < a ∧ 0 < b → 0 < a * b ∧ (x % (a * b)) % a = x % a

/-- Dividing by `c * d` equals dividing by `c`, then by `d`. -/
def spec_lemma_div_denominator (_impl : RepoImpl) : Prop :=
  ∀ (x : Int) (c : Int) (d : Int),
    0 ≤ x ∧ 0 < c ∧ 0 < d → c * d ≠ 0 ∧ (x / c) / d = x / (c * d)

/-- Multiplication by a nonnegative integer can be hoisted over division as an inequality. -/
def spec_lemma_mul_hoist_inequality (_impl : RepoImpl) : Prop :=
  ∀ (x : Int) (y : Int) (z : Int), 0 ≤ x ∧ 0 < z → x * (y / z) ≤ (x * y) / z

/-- Multiplying a nonnegative integer by a positive divisor divides back to the integer. -/
def spec_lemma_div_by_multiple (_impl : RepoImpl) : Prop :=
  ∀ (b : Int) (d : Int), 0 ≤ b ∧ 0 < d → (b * d) / d = b

/-- If `a <= b * c`, then `a / b <= c` for positive `b`. -/
def spec_lemma_multiply_divide_le (_impl : RepoImpl) : Prop :=
  ∀ (a : Int) (b : Int) (c : Int), 0 < b ∧ a ≤ b * c → a / b ≤ c

/-- If `a < b * c`, then `a / b < c` for positive `b`. -/
def spec_lemma_multiply_divide_lt (_impl : RepoImpl) : Prop :=
  ∀ (a : Int) (b : Int) (c : Int), 0 < b ∧ a < b * c → a / b < c

/-- Common factors can be factored out of a modulo operation. -/
def spec_lemma_truncate_middle (_impl : RepoImpl) : Prop :=
  ∀ (x : Int) (b : Int) (c : Int),
    0 ≤ x ∧ 0 < b ∧ 0 < c → 0 < b * c ∧ (b * x) % (b * c) = b * (x % c)

/-- Multiplying numerator and denominator by a positive integer preserves quotient. -/
def spec_lemma_div_multiples_vanish_quotient (_impl : RepoImpl) : Prop :=
  ∀ (x : Int) (a : Int) (d : Int),
    0 < x ∧ 0 ≤ a ∧ 0 < d → 0 < x * d ∧ a / d = (x * a) / (x * d)

/-- Remainder breakdown for a product of positive divisors. -/
def spec_lemma_breakdown (_impl : RepoImpl) : Prop :=
  ∀ (x : Int) (y : Int) (z : Int),
    0 ≤ x ∧ 0 < y ∧ 0 < z →
      0 < y * z ∧ x % (y * z) = y * ((x / y) % z) + x % y

/-- Expanded modulo breakdown for a product of positive divisors. -/
def spec_lemma_mod_breakdown (_impl : RepoImpl) : Prop :=
  ∀ (x : Int) (y : Int) (z : Int),
    0 ≤ x ∧ 0 < y ∧ 0 < z →
      y * z > 0 ∧ x % (y * z) = y * ((x / y) % z) + x % y
