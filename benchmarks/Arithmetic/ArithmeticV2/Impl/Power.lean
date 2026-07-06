/-!
# ArithmeticV2.Impl.Power

Exponentiation helper vocabulary translated from Verus `power.rs`. This module
has no scored executable APIs; the definitions here are frozen vocabulary used
by translated specifications.
-/


namespace ArithmeticV2

/--
This function performs exponentiation recursively, to compute `b` to the power
of a natural number `e`.
-/
def pow (b : Int) : Nat → Int
  | 0 => 1
  | e + 1 => b * pow b e

/--
Selected source item for the exponentiation broadcast group.
-/
def group_pow_properties : Prop := True

/--
Proof of various useful properties of `pow` (exponentiation).
-/
def helper_lemma_pow_properties_prove_pow_auto : Prop :=
  ∀ (x : Int),
    (pow x 0) = 1 ∧
    ∀ (x : Int),
      (pow x 1) = x ∧
      ∀ (x : Int) (y : Int),
        y = 0 →
          (pow x (Int.toNat y)) = 1 ∧
          ∀ (x : Int) (y : Int),
            y = 1 →
              (pow x (Int.toNat y)) = x ∧
              ∀ (x : Int) (y : Int),
                0 < x ∧ 0 < y →
                  x ≤ x * (Int.toNat y : Int) ∧
                  ∀ (x : Int) (y : Int),
                    0 < x ∧ 1 < y →
                      x < x * (Int.toNat y : Int) ∧
                      ∀ (x : Int) (y : Nat) (z : Nat),
                        pow x (y + z) = (pow x y) * (pow x z) ∧
                        ∀ (x : Int) (y : Nat) (z : Nat),
                          y ≥ z →
                            pow x (y - z) * (pow x z) = (pow x y) ∧
                            ∀ (x : Int) (y : Nat) (z : Nat),
                              pow (x * (y : Int)) z = (pow x z) * pow (y : Int) z

end ArithmeticV2
