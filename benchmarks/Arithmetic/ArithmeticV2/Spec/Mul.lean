import ArithmeticV2.Impl.Mul
import ArithmeticV2.Harness

/-!
# ArithmeticV2.Spec.Mul

Specifications for multiplication helper properties. Each `spec_*` is a
property over an arbitrary `impl : RepoImpl`; this module has no scored APIs, so
the properties are stated over the frozen helper vocabulary.

DO NOT MODIFY -- this file is frozen curator-given content.
-/

open ArithmeticV2

/-- Multiplying a nonnegative integer by `*` agrees with `mul_pos`. -/
def spec_lemma_mul_is_mul_pos (_impl : RepoImpl) : Prop :=
  ∀ (x : Int) (y : Int), x ≥ 0 → x * y = mul_pos x y

/-- Basic properties of multiplication by zero and one. -/
def spec_lemma_mul_basics (_impl : RepoImpl) : Prop :=
  ∀ (x : Int), 0 * x = 0 ∧ x * 0 = 0 ∧ x * 1 = x ∧ 1 * x = x

/-- Multiplying zero by any integer is zero. -/
def spec_lemma_mul_basics_1 (_impl : RepoImpl) : Prop :=
  ∀ (x : Int), 0 * x = 0

/-- Multiplying any integer by zero is zero. -/
def spec_lemma_mul_basics_2 (_impl : RepoImpl) : Prop :=
  ∀ (x : Int), x * 0 = 0

/-- Multiplying any integer by one on the right returns the integer. -/
def spec_lemma_mul_basics_3 (_impl : RepoImpl) : Prop :=
  ∀ (x : Int), x * 1 = x

/-- Multiplying any integer by one on the left returns the integer. -/
def spec_lemma_mul_basics_4 (_impl : RepoImpl) : Prop :=
  ∀ (x : Int), 1 * x = x

/-- A product is nonzero if and only if both factors are nonzero. -/
def spec_lemma_mul_nonzero (_impl : RepoImpl) : Prop :=
  ∀ (x : Int) (y : Int), x * y ≠ 0 ↔ x ≠ 0 ∧ y ≠ 0

/-- Multiplication is associative. -/
def spec_lemma_mul_is_associative (_impl : RepoImpl) : Prop :=
  ∀ (x : Int) (y : Int) (z : Int), x * (y * z) = (x * y) * z

/-- Multiplication is commutative. -/
def spec_lemma_mul_is_commutative (_impl : RepoImpl) : Prop :=
  ∀ (x : Int) (y : Int), x * y = y * x

/-- A nonnegative product of two nonzero integers is at least each factor. -/
def spec_lemma_mul_ordering (_impl : RepoImpl) : Prop :=
  ∀ (x : Int) (y : Int), x ≠ 0 ∧ y ≠ 0 ∧ 0 ≤ x * y → x * y ≥ x ∧ x * y ≥ y

/-- Multiplication by a nonnegative right factor preserves non-strict order. -/
def spec_lemma_mul_inequality (_impl : RepoImpl) : Prop :=
  ∀ (x : Int) (y : Int) (z : Int), x ≤ y ∧ z ≥ 0 → x * z ≤ y * z

/-- Multiplication by a positive right factor preserves strict order. -/
def spec_lemma_mul_strict_inequality (_impl : RepoImpl) : Prop :=
  ∀ (x : Int) (y : Int) (z : Int), x < y ∧ z > 0 → x * z < y * z

/-- Multiplication by a positive left factor preserves non-strict and strict order. -/
def spec_lemma_mul_left_inequality (_impl : RepoImpl) : Prop :=
  ∀ (x : Int) (y : Int) (z : Int), 0 < x → y ≤ z → x * y ≤ x * z ∧ y < z → x * y < x * z

/-- Equal products by the same nonzero factor have equal right factors. -/
def spec_lemma_mul_equality_converse (_impl : RepoImpl) : Prop :=
  ∀ (m : Int) (x : Int) (y : Int), m ≠ 0 ∧ m * x = m * y → x = y

/-- Multiplication inequality by a positive right factor reflects order. -/
def spec_lemma_mul_inequality_converse (_impl : RepoImpl) : Prop :=
  ∀ (x : Int) (y : Int) (z : Int), x * z ≤ y * z ∧ z > 0 → x ≤ y

/-- Strict multiplication inequality by a nonnegative right factor reflects order. -/
def spec_lemma_mul_strict_inequality_converse (_impl : RepoImpl) : Prop :=
  ∀ (x : Int) (y : Int) (z : Int), x * z < y * z ∧ z ≥ 0 → x < y

/-- Multiplication distributes over addition on the right. -/
def spec_lemma_mul_is_distributive_add (_impl : RepoImpl) : Prop :=
  ∀ (x : Int) (y : Int) (z : Int), x * (y + z) = x * y + x * z

/-- Multiplication distributes over addition on the left. -/
def spec_lemma_mul_is_distributive_add_other_way (_impl : RepoImpl) : Prop :=
  ∀ (x : Int) (y : Int) (z : Int), (y + z) * x = y * x + z * x

/-- Multiplication distributes over subtraction on the right. -/
def spec_lemma_mul_is_distributive_sub (_impl : RepoImpl) : Prop :=
  ∀ (x : Int) (y : Int) (z : Int), x * (y - z) = x * y - x * z

/-- A product of two positive integers is positive. -/
def spec_lemma_mul_strictly_positive (_impl : RepoImpl) : Prop :=
  ∀ (x : Int) (y : Int), 0 < x ∧ 0 < y → 0 < x * y

/-- Multiplication by an integer greater than one strictly increases a positive factor. -/
def spec_lemma_mul_strictly_increases (_impl : RepoImpl) : Prop :=
  ∀ (x : Int) (y : Int), 1 < x ∧ 0 < y → y < x * y

/-- Multiplication by a positive integer does not decrease a positive factor. -/
def spec_lemma_mul_increases (_impl : RepoImpl) : Prop :=
  ∀ (x : Int) (y : Int), 0 < x ∧ 0 < y → y ≤ x * y

/-- A product of two nonnegative integers is nonnegative. -/
def spec_lemma_mul_nonnegative (_impl : RepoImpl) : Prop :=
  ∀ (x : Int) (y : Int), 0 ≤ x ∧ 0 ≤ y → 0 ≤ x * y

/-- Negating either factor negates the product. -/
def spec_lemma_mul_unary_negation (_impl : RepoImpl) : Prop :=
  ∀ (x : Int) (y : Int), (-x) * y = -(x * y) ∧ -(x * y) = x * (-y)

/-- Multiplying two negated factors cancels the negations. -/
def spec_lemma_mul_cancels_negatives (_impl : RepoImpl) : Prop :=
  ∀ (x : Int) (y : Int), x * y = (-x) * (-y)

/-- Multiplication by `*` agrees with the recursive multiplication helper. -/
def spec_lemma_mul_is_mul_recursive (_impl : RepoImpl) : Prop :=
  ∀ (x : Int) (y : Int), x * y = mul_recursive x y

/-- Multiplication by zero on either side returns zero. -/
def spec_lemma_mul_by_zero_is_zero (_impl : RepoImpl) : Prop :=
  ∀ (x : Int), x * 0 = 0 ∧ 0 * x = 0

/-- Products of nonnegative bounded factors are bounded by the product of their bounds. -/
def spec_lemma_mul_upper_bound (_impl : RepoImpl) : Prop :=
  ∀ (x : Int) (xbound : Int) (y : Int) (ybound : Int),
    x ≤ xbound ∧ y ≤ ybound ∧ 0 ≤ x ∧ 0 ≤ y → x * y ≤ xbound * ybound

/-- Products of positive factors below exclusive bounds are bounded by predecessor bounds. -/
def spec_lemma_mul_strict_upper_bound (_impl : RepoImpl) : Prop :=
  ∀ (x : Int) (xbound : Int) (y : Int) (ybound : Int),
    x < xbound ∧ y < ybound ∧ 0 < x ∧ 0 < y → x * y ≤ (xbound - 1) * (ybound - 1)

/-- Multiplication distributes over subtraction on the left. -/
def spec_lemma_mul_is_distributive_sub_other_way (_impl : RepoImpl) : Prop :=
  ∀ (x : Int) (y : Int) (z : Int), (y - z) * x = y * x - z * x
