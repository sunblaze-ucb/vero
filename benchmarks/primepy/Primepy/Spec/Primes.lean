import Primepy.Harness

/-! # Primepy.Spec.Primes

Specs for the `Primes` module: `factor`, `check`, `factors`, `phi`,
`first`, `upto`, `between`.

DO NOT MODIFY — frozen curator-given content.
-/

/-- `d` is a nonzero divisor of `n`. -/
def spec_helper_divides (d n : Int) : Prop :=
  d ≠ 0 ∧ n % d = 0

/-- Mathematical primality model for integers. -/
def spec_helper_primeLike (p : Int) : Prop :=
  2 ≤ p ∧
    ∀ d : Int, 2 ≤ d → d < p → ¬ spec_helper_divides d p

/-- Every list element is prime-like. -/
def spec_helper_allPrimeLike : List Int → Prop
  | [] => True
  | p :: ps => spec_helper_primeLike p ∧ spec_helper_allPrimeLike ps

/-- Product of an integer list. -/
def spec_helper_productInt : List Int → Int
  | [] => 1
  | x :: xs => x * spec_helper_productInt xs

/-- The list is sorted in nondecreasing order. -/
def spec_helper_sortedNondecreasing : List Int → Prop
  | [] => True
  | [_] => True
  | x :: y :: xs => x ≤ y ∧ spec_helper_sortedNondecreasing (y :: xs)

/-- The list is sorted in strictly increasing order. -/
def spec_helper_strictlyIncreasing : List Int → Prop
  | [] => True
  | [_] => True
  | x :: y :: xs => x < y ∧ spec_helper_strictlyIncreasing (y :: xs)

/-- `factor n` is the smallest prime-like divisor of every input `n >= 2`. -/
def spec_factor_smallest_prime_divisor (impl : RepoImpl) : Prop :=
  ∀ n : Int, 2 ≤ n →
    spec_helper_primeLike (impl.primepy.factor n) ∧
    spec_helper_divides (impl.primepy.factor n) n ∧
    ∀ p : Int,
      spec_helper_primeLike p →
      spec_helper_divides p n →
      impl.primepy.factor n ≤ p

/-- `check` agrees exactly with the mathematical prime-like predicate. -/
def spec_check_iff_prime_like (impl : RepoImpl) : Prop :=
  ∀ n : Int, impl.primepy.check n = true ↔ spec_helper_primeLike n

/-- `factors n` is a sorted prime factorization whose product is `n`. -/
def spec_factors_product_prime_sorted (impl : RepoImpl) : Prop :=
  ∀ n : Int, 2 ≤ n →
    spec_helper_productInt (impl.primepy.factors n) = n ∧
    spec_helper_allPrimeLike (impl.primepy.factors n) ∧
    spec_helper_sortedNondecreasing (impl.primepy.factors n)

/-- The first factor agrees with `factor`, tying the factorization API to the
smallest-prime-factor API. -/
def spec_factors_head_agrees_with_factor (impl : RepoImpl) : Prop :=
  ∀ n : Int, 2 ≤ n →
    (impl.primepy.factors n).head? = some (impl.primepy.factor n)

/-- Euler's totient has the expected value on prime-like inputs. -/
def spec_phi_prime_case (impl : RepoImpl) : Prop :=
  ∀ n : Int, spec_helper_primeLike n → impl.primepy.phi n = n - 1

/-- Euler's totient counts the integers in `[1, n]` that are coprime to `n`. -/
def spec_phi_counts_coprime_range (impl : RepoImpl) : Prop :=
  ∀ n : Int, 1 ≤ n →
    impl.primepy.phi n =
      Int.ofNat
        (((List.range n.toNat).filter
          (fun k => Nat.gcd (k + 1) n.toNat == 1)).length)

/-- `first n` returns exactly `n` strictly increasing primes, and the returned
prefix agrees with `upto` through its last element. -/
def spec_first_prime_prefix (impl : RepoImpl) : Prop :=
  ∀ n : Nat,
    (impl.primepy.first n).length = n ∧
    spec_helper_strictlyIncreasing ((impl.primepy.first n).map Int.ofNat) ∧
    spec_helper_allPrimeLike ((impl.primepy.first n).map Int.ofNat) ∧
    ∀ last : Nat,
      (impl.primepy.first n).getLast? = some last →
      (impl.primepy.upto (Int.ofNat last)).map Int.toNat = impl.primepy.first n

/-- `upto n` returns exactly the strictly increasing prime-like integers at
most `n`. -/
def spec_upto_exact_prime_range (impl : RepoImpl) : Prop :=
  ∀ n : Int,
    spec_helper_strictlyIncreasing (impl.primepy.upto n) ∧
    ∀ p : Int,
      p ∈ impl.primepy.upto n ↔ spec_helper_primeLike p ∧ p ≤ n

/-- `between m n` is the lower-bound-exclusive view of `upto n`. -/
def spec_between_agrees_with_upto (impl : RepoImpl) : Prop :=
  ∀ m n : Int,
    impl.primepy.between m n =
      (impl.primepy.upto n).filter (fun p => decide (m < p))
