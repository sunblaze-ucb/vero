import SpecialNumbers.Harness

/-!
# SpecialNumbers.Spec.CarmichaelNumber

Specifications for Carmichael numbers and modular exponentiation.
Each `spec_*` is a property over an arbitrary `impl : RepoImpl`.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- The Carmichael predicate agrees with the repo's modular exponentiation on every coprime base. -/
def spec_carmichael_uses_power_and_gcd (impl : RepoImpl) : Prop :=
  ∀ n b : Int, n > 1 → 2 ≤ b → b < n →
    impl.specialNumbers.is_carmichael_number n = true →
    impl.specialNumbers.greatest_common_divisor b n = 1 →
    impl.specialNumbers.power b (n - 1) n = 1

/-- Modular exponentiation has the zero-exponent identity on every modulus. -/
def spec_power_zero_exponent (impl : RepoImpl) : Prop :=
  ∀ x m : Int, impl.specialNumbers.power x 0 m = 1

/-- Non-scored counterexample note: the classical theorem "Carmichael ⟹ composite" is false on the reference impl.
    The impl returns `true` for prime 5 (Fermat's little theorem holds for all coprime bases mod a prime).
    The first conjunct holds; the second asserts 5 has a small divisor, which is false since 5 is prime.
    Therefore this conjunction is unprovable on the canonical impl and should not be a scored spec. -/
def spec_carmichael_implies_composite (impl : RepoImpl) : Prop :=
  impl.specialNumbers.is_carmichael_number 5 = true ∧
  ((5 : Int) % 2 = 0 ∨ (5 : Int) % 3 = 0 ∨ (5 : Int) % 4 = 0)
