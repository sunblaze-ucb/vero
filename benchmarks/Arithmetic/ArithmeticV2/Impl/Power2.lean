import ArithmeticV2.Impl.Power

/-!
# ArithmeticV2.Impl.Power2

Power-of-two helper vocabulary translated from Verus `power2.rs`. This module
has no scored executable APIs; the definitions here are frozen vocabulary used
by translated specifications.
-/


namespace ArithmeticV2

/--
This function computes 2 to the power of the given natural number `e`.
-/
def pow2 (e : Nat) : Nat := Int.toNat (pow 2 e)

/--
Fuel-bounded recursive predicate for recognizing positive powers of 2.
-/
def isPow2Fuel : Int → Nat → Prop
  | _n, 0 => False
  | n, fuel + 1 =>
      if n <= 0 then False
      else if n = 1 then True
      else n % 2 = 0 ∧ isPow2Fuel (n / 2) fuel

/--
Returns true if the given integer is a power of 2, defined recursively.
-/
def is_pow2 (n : Int) : Prop :=
  isPow2Fuel n (n.natAbs + 1)

/--
Returns true if the given integer is a power of 2, defined existentially in
terms of `pow`.
-/
def is_pow2_exists (n : Int) : Prop := ∃ (i : Nat), pow 2 i = n

/--
Selected source item for the forward direction of recursive/existential
power-of-two equivalence.
-/
def helper_is_pow2_equiv_forward : Prop :=
  ∀ (n : Int), (is_pow2 n) → (is_pow2_exists n)

/--
Selected source item for the reverse direction of recursive/existential
power-of-two equivalence.
-/
def helper_is_pow2_equiv_reverse : Prop :=
  ∀ (n : Int), n > 0 ∧ (is_pow2_exists n) → (is_pow2 n)

end ArithmeticV2
