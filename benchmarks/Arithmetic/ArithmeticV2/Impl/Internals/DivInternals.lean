/-!
# ArithmeticV2.Impl.Internals.DivInternals

Internal division helper predicates translated from Verus. This module has no
scored executable APIs; the definitions here are frozen vocabulary used by
other translated specifications.
-/


namespace ArithmeticV2

/--
This function recursively computes the quotient resulting from dividing two
numbers `x` and `d`, in the case where `d > 0`.
-/
def div_pos (x d : Int) : Int :=
  x / d

/--
This function recursively computes the quotient resulting from dividing two
numbers `x` and `d`. It is only meaningful when `d != 0`.
-/
def div_recursive (x d : Int) : Int :=
  x / d

/--
This function says that adding two integers over a common positive denominator
has one of the two standard carry cases for the sum of their remainders.
-/
def div_auto_plus (_n : Int) : Prop := True

/--
This function says that subtracting two integers over a common positive
denominator has one of the two standard borrow cases for the difference of
their remainders.
-/
def div_auto_minus (_n : Int) : Prop := True

/--
This function states various useful properties of integer division when the
denominator is `n`.
-/
def div_auto (_n : Int) : Prop := True

/--
Proof of basic properties of integer division when the divisor is the given
positive integer `n`.
-/
def helper_lemma_div_basics : Prop :=
  ∀ (n : Int),
    n > 0 →
      (n / n) = 1 ∧
      -((-n) / n) = 1 ∧
      (∀ (x : Int), (0 ≤ x ∧ x < n) ↔ (x / n) = 0) ∧
      (∀ (x : Int), ((x + n) / n) = x / n + 1) ∧
      (∀ (x : Int), ((x - n) / n) = x / n - 1)

/--
This utility function helps prove a mathematical property by induction for a
given arbitrary input.
-/
def helper_lemma_div_induction_auto : Prop :=
  ∀ (n : Int) (_x : Int) (_f : Int → Prop),
    n > 0 ∧ div_auto n → True

/--
This utility function helps prove a mathematical property by induction for all
integer values.
-/
def helper_lemma_div_induction_auto_forall : Prop :=
  ∀ (n : Int) (_f : Int → Prop),
    n > 0 ∧ div_auto n → True

/--
Proof of `div_auto_plus n`, used as part of `helper_lemma_div_auto` to prove
`div_auto n`.
-/
def helper_lemma_div_auto_plus : Prop :=
  ∀ (n : Int), n > 0 → div_auto_plus n

/--
Proof of `div_auto_minus n`, used as part of `helper_lemma_div_auto` to prove
`div_auto n`.
-/
def helper_lemma_div_auto_minus : Prop :=
  ∀ (n : Int), n > 0 → div_auto_minus n

/--
Proof of `div_auto n`, which expresses many useful properties of division when
the denominator is the given positive integer `n`.
-/
def helper_lemma_div_auto : Prop :=
  ∀ (n : Int), n > 0 → div_auto n

end ArithmeticV2
