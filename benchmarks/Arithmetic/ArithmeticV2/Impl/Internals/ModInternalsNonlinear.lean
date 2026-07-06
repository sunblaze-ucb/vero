/-!
# ArithmeticV2.Impl.Internals.ModInternalsNonlinear

Internal modulo helper predicates translated from Verus. This module has no
scored executable APIs; the definitions here are frozen vocabulary used by
other translated specifications.
-/


namespace ArithmeticV2

/--
Computes `x % y`. This mirrors the Verus functional trigger helper used where a
functional form of modulo is needed.
-/
def modulus (x y : Int) : Int := x % y

/--
Proof that 0 modulo any positive integer `m` is 0.
-/
def helper_lemma_mod_of_zero_is_zero : Prop :=
  ∀ (m : Int), 0 < m → (0 : Int) % m = (0 : Int)

/--
Proof of the fundamental theorem of division and modulo: for any nonzero
divisor `d` and any integer `x`, `x` is equal to `d * (x / d) + x % d`.
-/
def helper_lemma_fundamental_div_mod : Prop :=
  ∀ (x : Int) (d : Int), d ≠ 0 → x = d * (x / d) + (x % d)

/--
Proof that 0 modulo any positive integer is 0, using the functional modulo
helper as the trigger-shaped vocabulary.
-/
def helper_lemma_0_mod_anything : Prop :=
  ∀ (m : Int), m > 0 → (modulus 0 m) = 0

/--
Proof that a natural number `x` divided by a larger natural number `m` gives a
remainder equal to `x`.
-/
def helper_lemma_small_mod : Prop :=
  ∀ (x : Nat) (m : Nat), x < m ∧ 0 < m → modulus (x : Int) (m : Int) = (x : Int)

/--
Proof of Euclid's division lemma: any integer `x` modulo any positive integer
`m` is in the half-open range `[0, m)`.
-/
def helper_lemma_mod_range : Prop :=
  ∀ (x : Int) (m : Int), m > 0 → 0 ≤ (modulus x m) ∧ (modulus x m) < m

end ArithmeticV2
