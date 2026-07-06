/-!
# ArithmeticV2.Impl.Internals.DivInternalsNonlinear

Internal nonlinear division helper predicates translated from Verus. This module
has no scored executable APIs; the definitions here are frozen vocabulary used
by other translated specifications.
-/


namespace ArithmeticV2

/--
Proof that 0 divided by any given integer `d` is 0.
-/
def helper_lemma_div_of0 : Prop := ∀ (d : Int), d ≠ (0 : Int) → (0 : Int) / d = (0 : Int)

/--
Proof that any given integer `d` divided by itself is 1.
-/
def helper_lemma_div_by_self : Prop := ∀ (d : Int), d ≠ 0 → d / d = 1

/--
Proof that dividing a non-negative integer by a larger integer results in a
quotient of 0.
-/
def helper_lemma_small_div : Prop :=
  ∀ (x : Int) (d : Int), (0 ≤ x ∧ x < d) ∧ d > 0 → (x / d) = 0

end ArithmeticV2
