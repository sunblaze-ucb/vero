/-!
# ArithmeticV2.Impl.Internals.GeneralInternals

General internal arithmetic helper predicates translated from Verus. This
module has no scored executable APIs; the definitions here are frozen
vocabulary used by other translated specifications.
-/


namespace ArithmeticV2

/--
Computes the proposition `x <= y`. This mirrors the Verus functional
trigger helper used where a functional form of `<=` is needed.
-/
def is_le (x y : Int) : Prop := x ≤ y

/--
Nonnegative case helper for integer induction by steps of positive `n`.
-/
def helper_lemma_induction_helper_pos : Prop :=
  ∀ (n : Int) (f : Int → Prop) (x : Int),
    x ≥ 0 ∧
    n > 0 ∧
    (∀ (i : Int), (0 ≤ i ∧ i < n) → f i) ∧
    (∀ (i : Int), i ≥ 0 ∧ f i → f (i + n)) ∧
    (∀ (i : Int), i < n ∧ f i → f (i - n)) →
      f x

/--
Negative case helper for integer induction by steps of positive `n`.
-/
def helper_lemma_induction_helper_neg : Prop :=
  ∀ (n : Int) (f : Int → Prop) (x : Int),
    x < 0 ∧
    n > 0 ∧
    (∀ (i : Int), (0 ≤ i ∧ i < n) → f i) ∧
    (∀ (i : Int), i ≥ 0 ∧ f i → f (i + n)) ∧
    (∀ (i : Int), i < n ∧ f i → f (i - n)) →
      f x

/--
Integer induction helper by positive step `n`, with base cases for
`0 <= i < n` and inductive steps upward and downward.
-/
def helper_lemma_induction_helper : Prop :=
  ∀ (n : Int) (f : Int → Prop) (x : Int),
    n > 0 ∧
    (∀ (i : Int), (0 ≤ i ∧ i < n) → f i) ∧
    (∀ (i : Int), i ≥ 0 ∧ f i → f (i + n)) ∧
    (∀ (i : Int), i < n ∧ f i → f (i - n)) →
      f x

end ArithmeticV2
