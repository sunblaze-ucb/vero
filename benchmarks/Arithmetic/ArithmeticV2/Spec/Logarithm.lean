import ArithmeticV2.Impl.Logarithm
import ArithmeticV2.Harness

/-!
# ArithmeticV2.Spec.Logarithm

Specifications for integer logarithm helper properties. Each `spec_*` is a
property over an arbitrary `impl : RepoImpl`; this module has no scored APIs, so
the properties are stated over the frozen helper vocabulary.

DO NOT MODIFY -- this file is frozen curator-given content.
-/

open ArithmeticV2

/--
Proof that since `pow` is less than `base`, its logarithm in that base is 0.
-/
def spec_lemma_log0 (_impl : RepoImpl) : Prop :=
  ∀ (base : Int) (pow : Int), base > 1 ∧ (0 ≤ pow ∧ pow < base) → (log base pow) = 0

/--
Proof that since `pow` is greater than or equal to `base`, its logarithm in that
base is 1 more than the logarithm of `pow / base`.
-/
def spec_lemma_log_s (_impl : RepoImpl) : Prop :=
  ∀ (base : Int) (pow : Int),
    base > 1 ∧ pow ≥ base →
      pow / base ≥ 0 ∧ (log base pow) = 1 + (log base (pow / base))

/--
Proof that the integer logarithm is always nonnegative. Specifically,
`log(base, pow) >= 0`.
-/
def spec_lemma_log_nonnegative (_impl : RepoImpl) : Prop :=
  ∀ (base : Int) (pow : Int), base > 1 ∧ 0 ≤ pow → (log base pow) ≥ 0

/--
Proof that since `pow1` is less than or equal to `pow2`, the integer logarithm
of `pow1` in base `base` is less than or equal to that of `pow2`.
-/
def spec_lemma_log_is_ordered (_impl : RepoImpl) : Prop :=
  ∀ (base : Int) (pow1 : Int) (pow2 : Int),
    base > 1 ∧ (0 ≤ pow1 ∧ pow1 ≤ pow2) → (log base pow1) ≤ (log base pow2)

/--
Proof that the integer logarithm of `pow(base, n)` in base `base` is `n`.
-/
def spec_lemma_log_pow (_impl : RepoImpl) : Prop :=
  ∀ (base : Int) (n : Nat), base > 1 → log base (pow base n) = (n : Int)
