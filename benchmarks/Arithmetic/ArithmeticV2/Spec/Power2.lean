import ArithmeticV2.Impl.Power2
import ArithmeticV2.Harness

/-!
# ArithmeticV2.Spec.Power2

Specifications for power-of-two helper properties. Each `spec_*` is a property
over an arbitrary `impl : RepoImpl`; this module has no scored APIs, so the
properties are stated over the frozen helper vocabulary.

DO NOT MODIFY -- this file is frozen curator-given content.
-/

open ArithmeticV2

/--
Proof that 2 to the power of any natural number (specifically, `e`) is
positive.
-/
def spec_lemma_pow2_pos (_impl : RepoImpl) : Prop :=
  ∀ (e : Nat), (pow2 e) > 0

/-- Proof that `pow2(e)` is equivalent to `pow(2, e)`. -/
def spec_lemma_pow2 (_impl : RepoImpl) : Prop :=
  ∀ (e : Nat), (pow2 e : Int) = (pow 2 e)

/--
Proof establishing the concrete values for powers of 2 from 0 to 27.
-/
def spec_lemma2_to64 (_impl : RepoImpl) : Prop :=
  (pow2 0) = 0x1 ∧ (pow2 1) = 0x2 ∧ (pow2 2) = 0x4 ∧ (pow2 3) = 0x8 ∧
  (pow2 4) = 0x10 ∧ (pow2 5) = 0x20 ∧ (pow2 6) = 0x40 ∧ (pow2 7) = 0x80 ∧
  (pow2 8) = 0x100 ∧ (pow2 9) = 0x200 ∧ (pow2 10) = 0x400 ∧ (pow2 11) = 0x800 ∧
  (pow2 12) = 0x1000 ∧ (pow2 13) = 0x2000 ∧ (pow2 14) = 0x4000 ∧ (pow2 15) = 0x8000 ∧
  (pow2 16) = 0x10000 ∧ (pow2 17) = 0x20000 ∧ (pow2 18) = 0x40000 ∧ (pow2 19) = 0x80000 ∧
  (pow2 20) = 0x100000 ∧ (pow2 21) = 0x200000 ∧ (pow2 22) = 0x400000 ∧ (pow2 23) = 0x800000 ∧
  (pow2 24) = 0x1000000 ∧ (pow2 25) = 0x2000000 ∧ (pow2 26) = 0x4000000 ∧
  (pow2 27) = 0x8000000

/--
Proof establishing the concrete values for powers of 2 from 33 to 60.
-/
def spec_lemma2_to64_rest (_impl : RepoImpl) : Prop :=
  (pow2 33) = 0x200000000 ∧ (pow2 34) = 0x400000000 ∧ (pow2 35) = 0x800000000 ∧
  (pow2 36) = 0x1000000000 ∧ (pow2 37) = 0x2000000000 ∧ (pow2 38) = 0x4000000000 ∧
  (pow2 39) = 0x8000000000 ∧ (pow2 40) = 0x10000000000 ∧ (pow2 41) = 0x20000000000 ∧
  (pow2 42) = 0x40000000000 ∧ (pow2 43) = 0x80000000000 ∧ (pow2 44) = 0x100000000000 ∧
  (pow2 45) = 0x200000000000 ∧ (pow2 46) = 0x400000000000 ∧ (pow2 47) = 0x800000000000 ∧
  (pow2 48) = 0x1000000000000 ∧ (pow2 49) = 0x2000000000000 ∧
  (pow2 50) = 0x4000000000000 ∧ (pow2 51) = 0x8000000000000 ∧
  (pow2 52) = 0x10000000000000 ∧ (pow2 53) = 0x20000000000000 ∧
  (pow2 54) = 0x40000000000000 ∧ (pow2 55) = 0x80000000000000 ∧
  (pow2 56) = 0x100000000000000 ∧ (pow2 57) = 0x200000000000000 ∧
  (pow2 58) = 0x400000000000000 ∧ (pow2 59) = 0x800000000000000 ∧
  (pow2 60) = 0x1000000000000000

/--
Proof that the recursive and existential specifications for `is_pow2` are
equivalent.
-/
def spec_is_pow2_equiv (_impl : RepoImpl) : Prop :=
  ∀ (n : Int), (is_pow2 n) ↔ (is_pow2_exists n)

/-- Proof relating 2^e to 2^(e-1). -/
def spec_lemma_pow2_unfold (_impl : RepoImpl) : Prop :=
  ∀ (e : Nat), e > 0 → (pow2 e) = 2 * pow2 ((e - 1))

/-- Proof that `2^(e1 + e2)` is equivalent to `2^e1 * 2^e2`. -/
def spec_lemma_pow2_adds (_impl : RepoImpl) : Prop :=
  ∀ (e1 : Nat) (e2 : Nat), (pow2 (e1 + e2)) = (pow2 e1) * (pow2 e2)

/--
Proof that, as long as `e1 <= e2`, `2^(e2 - e1)` is equivalent to
`2^e2 / 2^e1`.
-/
def spec_lemma_pow2_subtracts (_impl : RepoImpl) : Prop :=
  ∀ (e1 : Nat) (e2 : Nat), e1 ≤ e2 →
    (pow2 (e2 - e1) = (pow2 e2) / (pow2 e1)) ∧
      0 < pow2 (e2 - e1)

/-- Proof that if `e1 < e2` then `2^e1 < 2^e2`. -/
def spec_lemma_pow2_strictly_increases (_impl : RepoImpl) : Prop :=
  ∀ (e1 : Nat) (e2 : Nat), e1 < e2 → (pow2 e1) < (pow2 e2)
