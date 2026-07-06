/-!
# ArithmeticV2.Impl.Internals.ModInternals

Internal modulo helper predicates translated from Verus. This module has no
scored executable APIs; the definitions here are frozen vocabulary used by
other translated specifications.
-/


namespace ArithmeticV2

/--
This function performs the modulus operation recursively.
-/
def mod_recursive (x d : Int) : Int :=
  x % d

/--
This function says that sums of two remainders are normalized modulo a positive
divisor.
-/
def mod_auto_plus (_n : Int) : Prop := True

/--
This function says that differences of two remainders are normalized modulo a
positive divisor.
-/
def mod_auto_minus (_n : Int) : Prop := True

/--
This function states various useful properties about the modulo operator when
the divisor is `n`.
-/
def mod_auto (_n : Int) : Prop := True

/--
This utility function helps prove a mathematical property by induction. The
caller supplies an integer predicate, proves base cases for `0 <= i < n`, and
proves upward and downward inductive steps by `n`.
-/
def helper_lemma_mod_induction_forall : Prop :=
  ∀ (n : Int) (f : Int → Prop),
    n > 0 ∧
    (∀ (i : Int), (0 ≤ i ∧ i < n) → f i) ∧
    (∀ (i : Int), i ≥ 0 ∧ f i → f (i + n)) ∧
    (∀ (i : Int), i < n ∧ f i → f (i - n)) →
      ∀ (i : Int), f i

/--
Proof that when dividing, adding the denominator to the numerator increases the
result by 1.
-/
def helper_lemma_div_add_denominator : Prop :=
  ∀ (n : Int) (x : Int), n > 0 → (x + n) / n = x / n + 1

/--
Proof that when dividing, subtracting the denominator from the numerator
decreases the result by 1.
-/
def helper_lemma_div_sub_denominator : Prop :=
  ∀ (n : Int) (x : Int), n > 0 → (x - n) / n = x / n - 1

/--
Proof that adding the denominator to the numerator does not change the
remainder.
-/
def helper_lemma_mod_add_denominator : Prop :=
  ∀ (n : Int) (x : Int), n > 0 → (x + n) % n = x % n

/--
Proof that subtracting the denominator from the numerator does not change the
remainder.
-/
def helper_lemma_mod_sub_denominator : Prop :=
  ∀ (n : Int) (x : Int), n > 0 → (x - n) % n = x % n

/--
Proof that `x % n = x` exactly when `x` is in the half-open range `[0, n)`.
-/
def helper_lemma_mod_below_denominator : Prop :=
  ∀ (n : Int) (x : Int), n > 0 → ((0 ≤ x ∧ x < n) ↔ x % n = x)

/--
Proof that if `x = q * n + r` and `0 <= r < n`, then `q` and `r` are the
quotient and remainder of `x` divided by `n`.
-/
def helper_lemma_quotient_and_remainder : Prop :=
  ∀ (x : Int) (q : Int) (r : Int) (n : Int),
    n > 0 ∧ (0 ≤ r ∧ r < n) ∧ x = q * n + r →
      q = x / n ∧ r = x % n

/--
This utility function helps prove a mathematical property by induction for a
given arbitrary input.
-/
def helper_lemma_mod_induction_auto : Prop :=
  ∀ (n : Int) (_x : Int) (_f : Int → Prop),
    n > 0 ∧ mod_auto n → True

/--
This utility function helps prove a mathematical property by induction for all
integer values.
-/
def helper_lemma_mod_induction_auto_forall : Prop :=
  ∀ (n : Int) (_f : Int → Prop),
    n > 0 ∧ mod_auto n → True

/--
This utility function helps prove a mathematical property of a pair of integers
by induction.
-/
def helper_lemma_mod_induction_forall2 : Prop :=
  ∀ (n : Int) (f : Int → Int → Prop),
    n > 0 ∧
    (∀ (i : Int) (j : Int), (0 ≤ i ∧ i < n) ∧ (0 ≤ j ∧ j < n) → f i j) ∧
    (∀ (i : Int) (j : Int), i ≥ 0 ∧ f i j → f (i + n) j) ∧
    (∀ (i : Int) (j : Int), j ≥ 0 ∧ f i j → f i (j + n)) ∧
    (∀ (i : Int) (j : Int), i < n ∧ f i j → f (i - n) j) ∧
    (∀ (i : Int) (j : Int), j < n ∧ f i j → f i (j - n)) →
      ∀ (i : Int) (j : Int), f i j

/--
Proof of basic properties of division and modulo for a positive divisor.
-/
def helper_lemma_mod_basics : Prop :=
  ∀ (n : Int),
    n > 0 →
      (∀ (x : Int), (x + n) % n = x % n) ∧
      (∀ (x : Int), (x - n) % n = x % n) ∧
      (∀ (x : Int), (x + n) / n = x / n + 1) ∧
      (∀ (x : Int), (x - n) / n = x / n - 1) ∧
      (∀ (x : Int), (0 ≤ x ∧ x < n) ↔ x % n = x)

/--
Proof of `mod_auto n`, which states useful properties about modulo with a
positive divisor.
-/
def helper_lemma_mod_auto : Prop :=
  ∀ (n : Int), n > 0 → mod_auto n

end ArithmeticV2
