import ArithmeticV2.Impl.Internals.MulInternals

/-!
# ArithmeticV2.Impl.Mul

Multiplication helper vocabulary translated from Verus `mul.rs`. This module
has no scored executable APIs; the definitions here are frozen vocabulary used
by translated specifications.
-/


namespace ArithmeticV2

/-- Selected source item for the multiplication basics broadcast group. -/
def group_mul_basics : Prop := True

/-- Selected source item for the multiplication distributivity broadcast group. -/
def group_mul_is_distributive : Prop := True

/-- Selected source item for the commutative-and-distributive broadcast group. -/
def group_mul_is_commutative_and_distributive : Prop := True

/-- Selected source item for the multiplication properties broadcast group. -/
def group_mul_properties : Prop := True

/--
Proof that multiplication is commutative, distributes over addition, and
distributes over subtraction in the source's selected cases.
-/
def helper_lemma_mul_is_distributive : Prop :=
  ∀ (x : Int) (y : Int) (z : Int),
    x * (y + z) = x * y + x * z ∧
    x * (y - z) = x * y - x * z ∧
    (y + z) * x = y * x + z * x ∧
    (y - z) * x = y * x - z * x ∧
    x * (y + z) = (y + z) * x ∧
    x * (y - z) = (y - z) * x ∧
    x * y = y * x ∧
    x * z = z * x

/--
Selected source item proving that the multiplication broadcast group provides
the automatic multiplication properties used by downstream proofs.
-/
def helper_lemma_mul_properties_prove_mul_properties_auto : Prop :=
  (∀ (x : Int) (y : Int), x * y = y * x) ∧
  (∀ (x : Int), x * 1 = x ∧ 1 * x = x) ∧
  (∀ (x : Int) (y : Int) (z : Int), x < y ∧ z > 0 → x * z < y * z) ∧
  (∀ (x : Int) (y : Int) (z : Int), x ≤ y ∧ z ≥ 0 → x * z ≤ y * z) ∧
  (∀ (x : Int) (y : Int) (z : Int), x * (y + z) = x * y + x * z) ∧
  (∀ (x : Int) (y : Int) (z : Int), x * (y - z) = x * y - x * z) ∧
  (∀ (x : Int) (y : Int) (z : Int), (y + z) * x = y * x + z * x) ∧
  (∀ (x : Int) (y : Int) (z : Int), (y - z) * x = y * x - z * x) ∧
  (∀ (x : Int) (y : Int) (z : Int), x * (y * z) = (x * y) * z) ∧
  (∀ (x : Int) (y : Int), x * y ≠ 0 ↔ x ≠ 0 ∧ y ≠ 0) ∧
  (∀ (x : Int) (y : Int), 0 ≤ x ∧ 0 ≤ y → 0 ≤ x * y) ∧
  (∀ (x : Int) (y : Int), 0 < x ∧ 0 < y ∧ 0 ≤ x * y → x ≤ x * y ∧ y ≤ x * y) ∧
  (∀ (x : Int) (y : Int), 1 < x ∧ 0 < y → y < x * y) ∧
  (∀ (x : Int) (y : Int), 0 < x ∧ 0 < y → y ≤ x * y) ∧
  (∀ (x : Int) (y : Int), 0 < x ∧ 0 < y → 0 < x * y)

end ArithmeticV2
