/-!
# ArithmeticV2.Impl.Internals.MulInternalsNonlinear

Internal nonlinear multiplication helper predicates translated from Verus. This
module has no scored executable APIs; the definitions here are frozen vocabulary
used by other translated specifications.
-/


namespace ArithmeticV2

/--
Proof that multiplying two positive integers `x` and `y` will result in a
positive integer.
-/
def helper_lemma_mul_strictly_positive : Prop :=
  ∀ (x : Int) (y : Int), (0 < x ∧ 0 < y) → (0 < x * y)

/--
Proof that `x` and `y` are both nonzero if and only if `x * y` is nonzero.
-/
def helper_lemma_mul_nonzero : Prop :=
  ∀ (x : Int) (y : Int), x * y ≠ 0 ↔ x ≠ 0 ∧ y ≠ 0

/--
Proof that multiplication is associative in this specific case, i.e., that
`x * y * z` is the same no matter which of the two multiplications is done
first.
-/
def helper_lemma_mul_is_associative : Prop :=
  ∀ (x : Int) (y : Int) (z : Int), x * (y * z) = (x * y) * z

/--
Proof that multiplication distributes over addition in this specific case, i.e.,
that `x * (y + z)` equals `x * y` plus `x * z`.
-/
def helper_lemma_mul_is_distributive_add : Prop :=
  ∀ (x : Int) (y : Int) (z : Int), x * (y + z) = x * y + x * z

/--
Proof that the if the product of two nonzero integers `x` and `y` is
nonnegative, then it's greater than or equal to each of `x` and `y`.
-/
def helper_lemma_mul_ordering : Prop :=
  ∀ (x : Int) (y : Int), x ≠ 0 ∧ y ≠ 0 ∧ 0 ≤ x * y → x * y ≥ x ∧ x * y ≥ y

/--
Proof that multiplying by a positive integer preserves inequality in this
specific case, i.e., that since `x < y` and `z > 0` we can conclude that
`x * z < y * z`.
-/
def helper_lemma_mul_strict_inequality : Prop :=
  ∀ (x : Int) (y : Int) (z : Int), x < y ∧ z > 0 → x * z < y * z

end ArithmeticV2
