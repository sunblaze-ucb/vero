import ArithmeticV2.Impl.Power
import ArithmeticV2.Harness

/-!
# ArithmeticV2.Spec.Power

Specifications for exponentiation helper properties. Each `spec_*` is a
property over an arbitrary `impl : RepoImpl`; this module has no scored APIs, so
the properties are stated over the frozen helper vocabulary.

DO NOT MODIFY -- this file is frozen curator-given content.
-/

open ArithmeticV2

/-- Proof that the given integer `b` to the power of 0 is 1. -/
def spec_lemma_pow0 (_impl : RepoImpl) : Prop :=
  ∀ (b : Int), (pow b 0) = 1

/-- Proof that 0 to the power of the given positive integer `e` is 0. -/
def spec_lemma0_pow (_impl : RepoImpl) : Prop :=
  ∀ (e : Nat), e > 0 → (pow 0 e) = 0

/-- Proof that 1 to the power of the given natural number `e` is 1. -/
def spec_lemma1_pow (_impl : RepoImpl) : Prop :=
  ∀ (e : Nat), (pow 1 e) = 1

/-- Proof that taking the given number `x` to the power of 2 produces `x * x`. -/
def spec_lemma_square_is_pow2 (_impl : RepoImpl) : Prop :=
  ∀ (x : Int), (pow x 2) = x * x

/--
Proof that `a * b` to the power of `e` is equal to the product of `a` to the
power of `e` and `b` to the power of `e`.
-/
def spec_lemma_pow_distributes (_impl : RepoImpl) : Prop :=
  ∀ (a : Int) (b : Int) (e : Nat), (pow (a * b) e) = (pow a e) * (pow b e)

/--
Proof that exponentiation then modulo produces the same result as doing the
modulo first, then doing the exponentiation, then doing the modulo again.
-/
def spec_lemma_pow_mod_noop (_impl : RepoImpl) : Prop :=
  ∀ (b : Int) (e : Nat) (m : Int), m > 0 → (pow (b % m) e) % m = (pow b e) % m

/-- Proof that the given integer `b` to the power of 1 is `b`. -/
def spec_lemma_pow1 (_impl : RepoImpl) : Prop :=
  ∀ (b : Int), (pow b 1) = b

/--
Proof that taking the given positive integer `b` to the power of the given
natural number `n` produces a positive result.
-/
def spec_lemma_pow_positive (_impl : RepoImpl) : Prop :=
  ∀ (b : Int) (e : Nat), b > 0 → 0 < (pow b e)

/--
Proof that taking an integer `b` to the power of the sum of two natural numbers
`e1` and `e2` is equivalent to multiplying `b` to the power of `e1` by `b` to
the power of `e2`.
-/
def spec_lemma_pow_adds (_impl : RepoImpl) : Prop :=
  ∀ (b : Int) (e1 : Nat) (e2 : Nat), (pow b (e1 + e2)) = (pow b e1) * (pow b e2)

/--
Proof that if `e1 >= e2`, then `b` to the power of `e1` is equal to the product
of `b` to the power of `e1 - e2` and `b` to the power of `e2`.
-/
def spec_lemma_pow_sub_add_cancel (_impl : RepoImpl) : Prop :=
  ∀ (b : Int) (e1 : Nat) (e2 : Nat), e1 ≥ e2 → pow b (e1 - e2) * (pow b e2) = (pow b e1)

/--
Proof that `a` to the power of `b * c` is equal to the result of taking `a` to
the power of `b`, then taking that to the power of `c`.
-/
def spec_lemma_pow_multiplies (_impl : RepoImpl) : Prop :=
  ∀ (a : Int) (b : Nat) (c : Nat), 0 ≤ b * c ∧ pow (pow a b) c = pow a (b * c)

/--
Proof that a number greater than 1 raised to a power strictly increases as the
power strictly increases.
-/
def spec_lemma_pow_strictly_increases (_impl : RepoImpl) : Prop :=
  ∀ (b : Nat) (e1 : Nat) (e2 : Nat),
    1 < b ∧ e1 < e2 → pow (b : Int) e1 < pow (b : Int) e2

/--
Proof that if `e2 <= e1` and `x < pow(b, e1)`, then dividing `x` by
`pow(b, e2)` produces a result less than `pow(b, e1 - e2)`.
-/
def spec_lemma_pow_division_inequality (_impl : RepoImpl) : Prop :=
  ∀ (x : Nat) (b : Nat) (e1 : Nat) (e2 : Nat),
    b > 0 ∧ e2 ≤ e1 ∧ x < pow (b : Int) e1 →
      pow (b : Int) e2 > 0 ∧
      ((x : Int) / pow (b : Int) e2) < pow (b : Int) (e1 - e2)

/-- Proof that `pow(b, e)` modulo `b` is 0. -/
def spec_lemma_pow_mod (_impl : RepoImpl) : Prop :=
  ∀ (b : Nat) (e : Nat), b > 0 ∧ e > 0 → pow (b : Int) e % (b : Int) = 0

/--
Proof that, as long as `e1 <= e2`, taking a positive integer `b` to the power
of `e2 - e1` is equivalent to dividing `b` to the power of `e2` by `b` to the
power of `e1`.
-/
def spec_lemma_pow_subtracts (_impl : RepoImpl) : Prop :=
  ∀ (b : Int) (e1 : Nat) (e2 : Nat),
    b > 0 ∧ e1 ≤ e2 →
      (pow b e1) > 0 ∧
      pow b (e2 - e1) = (pow b e2) / (pow b e1) ∧
      (pow b e2) / (pow b e1) > 0

/--
Proof that a positive number raised to a power increases as the power
increases.
-/
def spec_lemma_pow_increases (_impl : RepoImpl) : Prop :=
  ∀ (b : Nat) (e1 : Nat) (e2 : Nat),
    b > 0 ∧ e1 ≤ e2 → pow (b : Int) e1 ≤ pow (b : Int) e2

/--
Proof that if the exponentiation of a number greater than 1 doesn't decrease
when the exponent changes, then the change isn't a decrease.
-/
def spec_lemma_pow_increases_converse (_impl : RepoImpl) : Prop :=
  ∀ (b : Nat) (e1 : Nat) (e2 : Nat),
    1 < b ∧ pow (b : Int) e1 ≤ pow (b : Int) e2 → e1 ≤ e2

/--
Proof that `(b^(xy))^z = (b^x)^(yz)`, given that `x * y` and `y * z` are
nonnegative and `b` is positive.
-/
def spec_lemma_pull_out_pows (_impl : RepoImpl) : Prop :=
  ∀ (b : Nat) (x : Nat) (y : Nat) (z : Nat),
    b > 0 →
      0 ≤ x * y ∧
      0 ≤ y * z ∧
      pow (pow (b : Int) (x * y)) z = pow (pow (b : Int) x) (y * z)

/--
Proof that if an exponentiation result strictly increases when the exponent
changes, then the change is an increase.
-/
def spec_lemma_pow_strictly_increases_converse (_impl : RepoImpl) : Prop :=
  ∀ (b : Nat) (e1 : Nat) (e2 : Nat),
    b > 0 ∧ pow (b : Int) e1 < pow (b : Int) e2 → e1 < e2
