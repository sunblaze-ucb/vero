import Dafnycrypto.Harness

/-!
# Dafnycrypto.Spec.Util.Math

Specifications for mathematical utilities. Each `spec_*` is a property over an
arbitrary `impl : RepoImpl`; theorem stubs live in `Dafnycrypto/Proof/Util/Math.lean`.

DO NOT MODIFY — this file is frozen curator-given content.
-/

def spec_vecMul_length (impl : RepoImpl) : Prop :=
  ∀ (left right : List Int),
    (impl.dafnyCrypto.vecMul left right).length = min left.length right.length

def spec_vecAdd_length (impl : RepoImpl) : Prop :=
  ∀ (left right : List Int),
    (impl.dafnyCrypto.vecAdd left right).length = min left.length right.length

/-- For all n and k, `pow n (k+2) = n*n * pow n k` and `pow n (k+1) = n * pow n k`
    (recurrence characterising the fast exponentiation algorithm). -/
def spec_lemmaPow (impl : RepoImpl) : Prop :=
  ∀ (n k : Nat),
    impl.dafnyCrypto.pow n (k + 2) = n * n * impl.dafnyCrypto.pow n k ∧
    impl.dafnyCrypto.pow n (k + 1) = n * impl.dafnyCrypto.pow n k

def spec_powN_length (impl : RepoImpl) : Prop :=
  ∀ (x n : Nat),
    (impl.dafnyCrypto.powN x n).length = n

def spec_modPow_lt_modulus (impl : RepoImpl) : Prop :=
  ∀ (n k m : Nat),
    0 < m → impl.dafnyCrypto.modPow n k m < m

def spec_gcdExtended_gcd (impl : RepoImpl) : Prop :=
  ∀ (a b : Nat),
    (impl.dafnyCrypto.gcdExtended a b).1 = Nat.gcd a b

/-- Every nonzero element in a prime field has a multiplicative inverse: if `IsPrime n`
    and `1 ≤ a < n`, then `inverse a n` is `some`. -/
def spec_primeFieldsHaveInverse (impl : RepoImpl) : Prop :=
  ∀ (a n : Nat),
    DafnyCrypto.IsPrime n → 1 ≤ a → a < n →
    impl.dafnyCrypto.inverse a n ≠ none
