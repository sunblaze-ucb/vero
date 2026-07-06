import Primefac.Harness

/-!
# Primefac.Spec.Factor

Specifications for the factorization operations. Each `spec_*` is a property
over an arbitrary `impl : RepoImpl`; an API is always reached through
`impl.primefac.<fn>`, never by calling the reference `Primefac.<fn>`
directly.

`spec_isprime_oracle` characterizes the primality test by the divisibility
relation `∣`: `isprime n = true ↔ 2 ≤ n ∧ ∀ d, d ∣ n → d = 1 ∨ d = n`.

`primefac n` is characterized by: its product is `n` (via `iterprod`), every
element is prime, and the list is sorted nondecreasing; `spec_primefac_unique`
states it is the unique such list. The defs below (`prodList`, `isSortedAsc`,
`countList`, `powNat`, `mergeList`, `hasNoAdjDup`) are the specification's own
ground truth and never refer to `impl`.

DO NOT MODIFY — frozen benchmark content.
-/

-- ── Frozen ground-truth machinery (DO NOT MODIFY) ──────────────

/-- The frozen running product: the specification's own ground truth for the
    product of a list, independent of any implementation. Used to express the
    factorization product law and the uniqueness law against a fixed `*`. -/
def prodList : List Nat → Nat
  | [] => 1
  | x :: xs => x * prodList xs

/-- `isSortedAsc xs`: whether `xs` is in nondecreasing order — every adjacent
    pair satisfies the frozen `≤`. The empty and singleton lists are sorted. -/
def isSortedAsc : List Nat → Bool
  | [] => true
  | [_] => true
  | x :: y :: rest => x ≤ y && isSortedAsc (y :: rest)

/-- `countList p xs`: how many times `p` occurs in `xs` (frozen `==`/filter).
    The specification's own ground-truth multiplicity counter used to state the
    per-prime valuation and additivity laws. Never refers to any implementation. -/
def countList (p : Nat) (xs : List Nat) : Nat := (xs.filter (· == p)).length

/-- `powNat p k`: the frozen `k`-th power `p^k` (`p^0 = 1`), built from the
    frozen `*`. Used to express the exact p-adic valuation of a prime factor. -/
def powNat (p : Nat) : Nat → Nat
  | 0 => 1
  | k + 1 => p * powNat p k

/-- `mergeSorted fuel xs ys`: the order-merge of two nondecreasing lists into one
    nondecreasing list, carried by a structural `fuel` argument. The
    specification's own ground-truth sorted multiset union under `≤`. -/
def mergeSorted : Nat → List Nat → List Nat → List Nat
  | 0, _, _ => []
  | _, [], ys => ys
  | _, xs, [] => xs
  | fuel + 1, x :: xs, y :: ys =>
      if x ≤ y then x :: mergeSorted fuel xs (y :: ys)
      else y :: mergeSorted fuel (x :: xs) ys

/-- `mergeList xs ys`: the order-merge of `xs` and `ys` with sufficient fuel.
    The frozen sorted multiset union the multiplicative merge law is stated
    against (`primefac (a*b)` is the merge of `primefac a` and `primefac b`). -/
def mergeList (xs ys : List Nat) : List Nat :=
  mergeSorted (xs.length + ys.length) xs ys

/-- `hasNoAdjDup xs`: whether no two **adjacent** elements of `xs` are equal
    (frozen `==`). On a sorted list this is exactly "no duplicates", the frozen
    ground truth for the squarefree characterization. -/
def hasNoAdjDup : List Nat → Bool
  | [] => true
  | [_] => true
  | x :: y :: rest => (!(x == y)) && hasNoAdjDup (y :: rest)

/-- `sumList xs`: the running sum of a `Nat` list (`0` on the empty list). The
    specification's own ground-truth total, used to state the aggregate exponent
    of a product of prime powers against the frozen `+`. -/
def sumList : List Nat → Nat
  | [] => 0
  | x :: xs => x + sumList xs

/-- `divisorCount n`: the number of positive divisors of `n` — the count of
    `d ∈ [1, n]` with `n % d = 0` (frozen `%`). The specification's own
    ground-truth divisor tally, independent of any factorization. -/
def divisorCount (n : Nat) : Nat :=
  ((List.range (n + 1)).filter (fun d => if d = 0 then false else n % d == 0)).length

-- ════════════════════════════════════════════════════════════════
-- isprime: the frozen-divisibility oracle and its completeness laws.
-- ════════════════════════════════════════════════════════════════

/-- Primality oracle: `isprime n = true` exactly when `n ≥ 2` and every divisor
    of `n` is `1` or `n` itself. -/
def spec_isprime_oracle (impl : RepoImpl) : Prop :=
  ∀ (n : Nat),
    impl.primefac.isprime n = true ↔ 2 ≤ n ∧ ∀ d, d ∣ n → d = 1 ∨ d = n

/-- `0` is not prime (a frozen base anchor of the predicate). -/
def spec_isprime_zero (impl : RepoImpl) : Prop :=
  impl.primefac.isprime 0 = false

/-- `1` is not prime: the unit is excluded, pinning the `2 ≤ n` lower edge. -/
def spec_isprime_one (impl : RepoImpl) : Prop :=
  impl.primefac.isprime 1 = false

/-- `2` is prime: the smallest prime. -/
def spec_isprime_two (impl : RepoImpl) : Prop :=
  impl.primefac.isprime 2 = true

/-- A prime is at least `2` (the lower edge, stated as a direct consequence). -/
def spec_isprime_ge_two (impl : RepoImpl) : Prop :=
  ∀ (n : Nat), impl.primefac.isprime n = true → 2 ≤ n

/-- A prime has no nontrivial divisor: for every `d` strictly between `1` and
    `n`, `d` does not divide `n`. -/
def spec_isprime_no_divisor (impl : RepoImpl) : Prop :=
  ∀ (n d : Nat),
    impl.primefac.isprime n = true → 2 ≤ d → d < n → ¬ d ∣ n

/-- Any `n ≥ 2` with no divisor strictly between `1` and `n` is prime — the
    converse of `spec_isprime_no_divisor`. -/
def spec_isprime_of_no_small_divisor (impl : RepoImpl) : Prop :=
  ∀ (n : Nat),
    2 ≤ n → (∀ d, 2 ≤ d → d < n → ¬ d ∣ n) → impl.primefac.isprime n = true

/-- Composite witness: a non-prime `n ≥ 2` has a nontrivial divisor — there
    exists `d` with `2 ≤ d < n` and `d ∣ n`. -/
def spec_isprime_has_divisor (impl : RepoImpl) : Prop :=
  ∀ (n : Nat),
    impl.primefac.isprime n = false → 2 ≤ n →
      ∃ d, 2 ≤ d ∧ d < n ∧ d ∣ n

-- ════════════════════════════════════════════════════════════════
-- iterprod: freezes the product operation the factorization rides on.
-- ════════════════════════════════════════════════════════════════

/-- `iterprod` of the empty list is `1` — freezes the product's unit. -/
def spec_iterprod_nil (impl : RepoImpl) : Prop :=
  impl.primefac.iterprod [] = 1

/-- The product step law: `iterprod (x :: xs) = x * iterprod xs`. -/
def spec_iterprod_cons (impl : RepoImpl) : Prop :=
  ∀ (x : Nat) (xs : List Nat),
    impl.primefac.iterprod (x :: xs) = x * impl.primefac.iterprod xs

/-- Product distributes over append:
    `iterprod (xs ++ ys) = iterprod xs * iterprod ys`. -/
def spec_iterprod_append (impl : RepoImpl) : Prop :=
  ∀ (xs ys : List Nat),
    impl.primefac.iterprod (xs ++ ys)
      = impl.primefac.iterprod xs * impl.primefac.iterprod ys

/-- `iterprod` agrees with the ground-truth `prodList` on every list. -/
def spec_iterprod_correct (impl : RepoImpl) : Prop :=
  ∀ (xs : List Nat), impl.primefac.iterprod xs = prodList xs

-- ════════════════════════════════════════════════════════════════
-- primefac: product = n, all elements prime, sorted; and the unique
-- such list (spec_primefac_unique).
-- ════════════════════════════════════════════════════════════════

/-- `primefac 1 = []` — the empty factorization of the unit (frozen base,
    consistent with `iterprod [] = 1`). -/
def spec_primefac_one (impl : RepoImpl) : Prop :=
  impl.primefac.primefac 1 = []

/-- Product law: the product of the factorization is `n` itself, for `n ≥ 1`. -/
def spec_primefac_product (impl : RepoImpl) : Prop :=
  ∀ (n : Nat), 1 ≤ n →
    impl.primefac.iterprod (impl.primefac.primefac n) = n

/-- All-prime law: every element of the factorization is prime, for `n ≥ 2`. -/
def spec_primefac_allprime (impl : RepoImpl) : Prop :=
  ∀ (n : Nat), 2 ≤ n →
    ∀ p, p ∈ impl.primefac.primefac n → impl.primefac.isprime p = true

/-- Sorted law: the factorization is in nondecreasing order. -/
def spec_primefac_sorted (impl : RepoImpl) : Prop :=
  ∀ (n : Nat), isSortedAsc (impl.primefac.primefac n) = true

/-- The factorization of any `n ≥ 2` is nonempty. -/
def spec_primefac_nonempty (impl : RepoImpl) : Prop :=
  ∀ (n : Nat), 2 ≤ n → impl.primefac.primefac n ≠ []

/-- Each factor is at least `2`. -/
def spec_primefac_ge_two (impl : RepoImpl) : Prop :=
  ∀ (n : Nat), 2 ≤ n →
    ∀ p, p ∈ impl.primefac.primefac n → 2 ≤ p

/-- Divisibility: every prime factor divides `n` (for `n ≥ 1`). -/
def spec_primefac_dvd (impl : RepoImpl) : Prop :=
  ∀ (n : Nat), 1 ≤ n →
    ∀ p, p ∈ impl.primefac.primefac n → p ∣ n

/-- Uniqueness: any sorted list of primes whose product is `n` equals
    `primefac n`. For `n ≥ 1` and any candidate `ps`, if every element of `ps`
    is prime, `ps` is sorted, and `iterprod ps = n`, then `ps = primefac n`. -/
def spec_primefac_unique (impl : RepoImpl) : Prop :=
  ∀ (n : Nat) (ps : List Nat), 1 ≤ n →
    (∀ p, p ∈ ps → impl.primefac.isprime p = true) →
    isSortedAsc ps = true →
    impl.primefac.iterprod ps = n →
      ps = impl.primefac.primefac n

/-- A prime factors to itself: if `n` is prime then `primefac n = [n]`. -/
def spec_primefac_prime_self (impl : RepoImpl) : Prop :=
  ∀ (n : Nat), impl.primefac.isprime n = true →
    impl.primefac.primefac n = [n]

/-- Prime-divisor membership: if `p` is prime and divides `n` (for `n ≥ 1`),
    then `p` appears in `primefac n` — the factorization omits no prime factor. -/
def spec_primefac_prime_mem (impl : RepoImpl) : Prop :=
  ∀ (n p : Nat), 1 ≤ n →
    impl.primefac.isprime p = true → p ∣ n →
      p ∈ impl.primefac.primefac n

-- ════════════════════════════════════════════════════════════════
-- Deep structural laws: uniqueness of the sorted prime list, the API
-- bridge to `isprime`, multiplicativity, and per-prime multiplicity.
-- ════════════════════════════════════════════════════════════════

/-- General uniqueness of the sorted prime list: any two sorted lists of primes
    with the same `iterprod` are equal. For candidates `ps`, `qs`, each
    all-prime and sorted, if `iterprod ps = iterprod qs` then `ps = qs`. -/
def spec_primefac_unique_general (impl : RepoImpl) : Prop :=
  ∀ (ps qs : List Nat),
    (∀ p, p ∈ ps → impl.primefac.isprime p = true) →
    isSortedAsc ps = true →
    (∀ q, q ∈ qs → impl.primefac.isprime q = true) →
    isSortedAsc qs = true →
    impl.primefac.iterprod ps = impl.primefac.iterprod qs →
      ps = qs

/-- Primality ⇔ singleton factorization: for `n ≥ 2`, `isprime n = true`
    exactly when `primefac n = [n]`. -/
def spec_isprime_iff_singleton (impl : RepoImpl) : Prop :=
  ∀ (n : Nat), 2 ≤ n →
    (impl.primefac.isprime n = true ↔ impl.primefac.primefac n = [n])

/-- Multiplicativity: the factorization of a product is the sorted merge of the
    factorizations of the factors. For `a, b ≥ 1`,
    `primefac (a * b) = mergeList (primefac a) (primefac b)`. -/
def spec_primefac_mul (impl : RepoImpl) : Prop :=
  ∀ (a b : Nat), 1 ≤ a → 1 ≤ b →
    impl.primefac.primefac (a * b)
      = mergeList (impl.primefac.primefac a) (impl.primefac.primefac b)

/-- Multiplicity additivity: for every `p`, the number of times `p` occurs in
    `primefac (a * b)` is the sum of its occurrences in `primefac a` and
    `primefac b`, for `a, b ≥ 1`. -/
def spec_primefac_count_mul (impl : RepoImpl) : Prop :=
  ∀ (a b p : Nat), 1 ≤ a → 1 ≤ b →
    countList p (impl.primefac.primefac (a * b))
      = countList p (impl.primefac.primefac a)
        + countList p (impl.primefac.primefac b)

/-- Exact p-adic valuation: for a prime `p` and `n ≥ 1`, with
    `k = countList p (primefac n)`, both `powNat p k ∣ n` and
    `¬ powNat p (k+1) ∣ n` hold — the multiplicity of `p` is exactly the largest
    power of `p` dividing `n`. -/
def spec_primefac_valuation (impl : RepoImpl) : Prop :=
  ∀ (n p : Nat), 1 ≤ n → impl.primefac.isprime p = true →
    powNat p (countList p (impl.primefac.primefac n)) ∣ n
    ∧ ¬ powNat p (countList p (impl.primefac.primefac n) + 1) ∣ n

/-- Squarefree characterization: for `n ≥ 1`, `primefac n` has no two equal
    adjacent entries exactly when no `d ≥ 2` has `d * d ∣ n`. -/
def spec_primefac_squarefree (impl : RepoImpl) : Prop :=
  ∀ (n : Nat), 1 ≤ n →
    (hasNoAdjDup (impl.primefac.primefac n) = true
      ↔ ∀ d, 2 ≤ d → ¬ d * d ∣ n)

/-- Ω-additivity: the total prime-factor count of a product is the sum of the
    counts of its factors. For `a, b ≥ 1`,
    `(primefac (a * b)).length = (primefac a).length + (primefac b).length`. -/
def spec_primefac_omega_mul (impl : RepoImpl) : Prop :=
  ∀ (a b : Nat), 1 ≤ a → 1 ≤ b →
    (impl.primefac.primefac (a * b)).length
      = (impl.primefac.primefac a).length + (impl.primefac.primefac b).length

/-- Prime-power factorization: for a prime `p` and any exponent `k`,
    `primefac (powNat p k) = List.replicate k p` — the factorization of `p ^ k`
    is exactly `k` copies of `p` (with `k = 0` giving `[]`). -/
def spec_primefac_prime_pow (impl : RepoImpl) : Prop :=
  ∀ (p k : Nat), impl.primefac.isprime p = true →
    impl.primefac.primefac (powNat p k) = List.replicate k p

/-- Exponent-scaled multiplicity: for `n ≥ 1`, every `p`, and every exponent
    `k`, `countList p (primefac (powNat n k)) = k * countList p (primefac n)`. -/
def spec_primefac_count_pow (impl : RepoImpl) : Prop :=
  ∀ (n k p : Nat), 1 ≤ n →
    countList p (impl.primefac.primefac (powNat n k))
      = k * countList p (impl.primefac.primefac n)

/-- Exponent-scaled Ω: for `n ≥ 1` and every exponent `k`,
    `(primefac (powNat n k)).length = k * (primefac n).length`, i.e.
    `Ω(n ^ k) = k · Ω(n)`. -/
def spec_primefac_omega_pow (impl : RepoImpl) : Prop :=
  ∀ (n k : Nat), 1 ≤ n →
    (impl.primefac.primefac (powNat n k)).length
      = k * (impl.primefac.primefac n).length

/-- Least prime factor: for every `n ≥ 2` there is a prime `q` occurring in
    `primefac n` that divides `n` and is no larger than any prime divisor of
    `n` — the smallest prime factor. -/
def spec_primefac_least (impl : RepoImpl) : Prop :=
  ∀ (n : Nat), 2 ≤ n →
    ∃ q, q ∈ impl.primefac.primefac n
      ∧ impl.primefac.isprime q = true
      ∧ q ∣ n
      ∧ ∀ d, impl.primefac.isprime d = true → d ∣ n → q ≤ d

-- ════════════════════════════════════════════════════════════════
-- Positional and count-transport laws.
-- ════════════════════════════════════════════════════════════════

/-- Head characterization: for `n ≥ 2`, the first entry of `primefac n` is `p`
    exactly when `p` is a prime divisor of `n` that is no larger than any prime
    divisor of `n`. -/
def spec_primefac_head_le_iff (impl : RepoImpl) : Prop :=
  ∀ (n p : Nat), 2 ≤ n →
    ((impl.primefac.primefac n).head? = some p ↔
      impl.primefac.isprime p = true ∧ p ∣ n ∧
        ∀ d, impl.primefac.isprime d = true → d ∣ n → p ≤ d)

/-- First-occurrence exposure: if `p` occurs in `primefac n`, then dropping as
    many leading entries as there are factors strictly smaller than `p` leaves a
    list whose head is `p`. -/
def spec_primefac_first_occurrence_index (impl : RepoImpl) : Prop :=
  ∀ (n p : Nat), p ∈ impl.primefac.primefac n →
    (List.drop (((impl.primefac.primefac n).filter (fun q => q < p)).length)
      (impl.primefac.primefac n)).head? = some p

/-- Prime-list multiplicity round trip: for any list `xs` of primes and any `p`,
    the multiplicity of `p` in the factorization of `iterprod xs` equals the
    number of times `p` occurs in `xs` itself. -/
def spec_primefac_prime_list_count (impl : RepoImpl) : Prop :=
  ∀ (xs : List Nat) (p : Nat),
    (∀ q, q ∈ xs → impl.primefac.isprime q = true) →
      countList p (impl.primefac.primefac (impl.primefac.iterprod xs))
        = countList p xs

/-- GCD multiplicity: for a prime `p` and `a, b ≥ 1`, the multiplicity of `p`
    in `primefac (Nat.gcd a b)` is the minimum of its multiplicities in
    `primefac a` and `primefac b`. -/
def spec_primefac_gcd_count_min (impl : RepoImpl) : Prop :=
  ∀ (a b p : Nat), 1 ≤ a → 1 ≤ b →
    countList p (impl.primefac.primefac (Nat.gcd a b))
      = Nat.min (countList p (impl.primefac.primefac a))
          (countList p (impl.primefac.primefac b))

-- ════════════════════════════════════════════════════════════════
-- Valuation transport, gcd/lcm conservation, positional blocks, and
-- the divisor-count aggregate.
-- ════════════════════════════════════════════════════════════════

/-- Packet aggregate: for a prime `p` and any list of exponents `ks`, the
    multiplicity of `p` in the factorization of `iterprod (ks.map (p ^ ·))`
    equals `sumList ks`. -/
def spec_primefac_prime_power_packet_count (impl : RepoImpl) : Prop :=
  ∀ (p : Nat) (ks : List Nat), impl.primefac.isprime p = true →
    countList p
      (impl.primefac.primefac
        (impl.primefac.iterprod (ks.map (fun k => powNat p k))))
      = sumList ks

/-- Filter transport: for any list `xs` of primes and any `p`, refactoring the
    product of the entries `≠ p` yields no `p`, and refactoring the product of
    the entries `= p` recovers exactly `countList p xs`. -/
def spec_primefac_refactor_filtered_prime_counts (impl : RepoImpl) : Prop :=
  ∀ (xs : List Nat) (p : Nat),
    (∀ q, q ∈ xs → impl.primefac.isprime q = true) →
      countList p
        (impl.primefac.primefac
          (impl.primefac.iterprod (xs.filter (fun q => !(q == p))))) = 0
      ∧ countList p
        (impl.primefac.primefac
          (impl.primefac.iterprod (xs.filter (fun q => q == p))))
        = countList p xs

/-- Contiguous block: if `p` occurs in `primefac n`, its occurrences form one
    contiguous run beginning right after the factors below `p`. With
    `start = #{q : q < p}` and `len = countList p`, the `len` entries from
    `start` are all `p`, and the entry just past them is not `p`. -/
def spec_primefac_factor_block (impl : RepoImpl) : Prop :=
  ∀ (n p : Nat), p ∈ impl.primefac.primefac n →
    let xs := impl.primefac.primefac n
    let start := (xs.filter (fun q => q < p)).length
    let len := countList p xs
    List.take len (List.drop start xs) = List.replicate len p
      ∧ (List.drop (start + len) xs).head? ≠ some p

/-- LCM multiplicity: for `a, b ≥ 1` and every `p`, the multiplicity of `p` in
    `primefac (Nat.lcm a b)` is the maximum of its multiplicities in
    `primefac a` and `primefac b`. -/
def spec_primefac_lcm_count_max (impl : RepoImpl) : Prop :=
  ∀ (a b p : Nat), 1 ≤ a → 1 ≤ b →
    countList p (impl.primefac.primefac (Nat.lcm a b))
      = Nat.max (countList p (impl.primefac.primefac a))
          (countList p (impl.primefac.primefac b))

/-- Coprimality ⇔ disjoint support: for `a, b ≥ 1`, `Nat.gcd a b = 1` exactly
    when no factor of `a` is also a factor of `b`. -/
def spec_primefac_gcd_one_iff_disjoint (impl : RepoImpl) : Prop :=
  ∀ (a b : Nat), 1 ≤ a → 1 ≤ b →
    (Nat.gcd a b = 1 ↔
      ∀ p, p ∈ impl.primefac.primefac a → p ∉ impl.primefac.primefac b)

/-- GCD/LCM conservation: for `a, b ≥ 1`, the total factor counts satisfy
    `(primefac (gcd a b)).length + (primefac (lcm a b)).length
      = (primefac a).length + (primefac b).length`. -/
def spec_primefac_omega_gcd_lcm_conservation (impl : RepoImpl) : Prop :=
  ∀ (a b : Nat), 1 ≤ a → 1 ≤ b →
    (impl.primefac.primefac (Nat.gcd a b)).length
      + (impl.primefac.primefac (Nat.lcm a b)).length
        = (impl.primefac.primefac a).length
          + (impl.primefac.primefac b).length

/-- Prime-power split: for `n ≥ 1` and a prime `p` with
    `k = countList p (primefac n)`, `primefac n` is the sorted merge of `k`
    copies of `p` with `primefac (n / p ^ k)`, and that quotient has no `p`. -/
def spec_primefac_split_exact_prime_power (impl : RepoImpl) : Prop :=
  ∀ (n p : Nat), 1 ≤ n → impl.primefac.isprime p = true →
    let k := countList p (impl.primefac.primefac n)
    impl.primefac.primefac n =
        mergeList (List.replicate k p)
          (impl.primefac.primefac (n / powNat p k))
      ∧ countList p (impl.primefac.primefac (n / powNat p k)) = 0

/-- Divisor-count aggregate: for `n ≥ 1`, `divisorCount n` equals the product
    over the distinct factors of `n` of `countList p (primefac n) + 1`. -/
def spec_primefac_divisor_count_product (impl : RepoImpl) : Prop :=
  ∀ (n : Nat), 1 ≤ n →
    divisorCount n
      = prodList ((impl.primefac.primefac n).eraseDups.map
          (fun p => countList p (impl.primefac.primefac n) + 1))

/-- Distinct-factor inclusion–exclusion: for `a, b ≥ 1`, the counts of distinct
    factors satisfy
    `#distinct (a*b) + #distinct (gcd a b) = #distinct a + #distinct b`. -/
def spec_primefac_distinct_mul_inclusion (impl : RepoImpl) : Prop :=
  ∀ (a b : Nat), 1 ≤ a → 1 ≤ b →
    (impl.primefac.primefac (a * b)).eraseDups.length
      + (impl.primefac.primefac (Nat.gcd a b)).eraseDups.length
        = (impl.primefac.primefac a).eraseDups.length
          + (impl.primefac.primefac b).eraseDups.length

-- ── Additional frozen ground-truth machinery (DO NOT MODIFY) ──

/-- `radList xs`: the product of the *distinct* entries of `xs` (frozen
    `eraseDups` then `prodList`). Applied to a factorization it is the radical
    (squarefree kernel) — the product of the distinct prime factors. -/
def radList (xs : List Nat) : Nat := prodList xs.eraseDups

/-- `tauList xs`: the product over the distinct entries of `xs` of
    `(multiplicity + 1)` (frozen `eraseDups`/`countList`/`prodList`). On a
    factorization this is the divisor-count product formula `∏ (eₚ + 1)`. -/
def tauList (xs : List Nat) : Nat :=
  prodList (xs.eraseDups.map (fun p => countList p xs + 1))

/-- `geoFactor p e`: the geometric sum `1 + p + ⋯ + p^e` (frozen `powNat`/
    `sumList`), the per-prime factor of the sum-of-divisors product formula. -/
def geoFactor (p e : Nat) : Nat :=
  sumList ((List.range (e + 1)).map (fun k => powNat p k))

/-- `divisorSum n`: the sum of the positive divisors of `n` — the total of the
    `d ∈ [1, n]` with `n % d = 0` (frozen `%`/`sumList`). The specification's
    own ground-truth σ, independent of any factorization. -/
def divisorSum (n : Nat) : Nat :=
  sumList ((List.range (n + 1)).filter
    (fun d => if d = 0 then false else n % d == 0))

-- ════════════════════════════════════════════════════════════════
-- Radical (squarefree kernel), divisor-count τ, and σ laws pinned to
-- the prime-factor multiset.
-- ════════════════════════════════════════════════════════════════

/-- Radical canonical form: for `n ≥ 1`, the factorization of the product of
    the distinct prime factors of `n` is exactly that duplicate-free factor
    list. -/
def spec_primefac_radical_factorization (impl : RepoImpl) : Prop :=
  ∀ (n : Nat), 1 ≤ n →
    impl.primefac.primefac (radList (impl.primefac.primefac n))
      = (impl.primefac.primefac n).eraseDups

/-- Radical divides: for `n ≥ 1`, the product of the distinct prime factors of
    `n` divides `n`. -/
def spec_primefac_radical_dvd (impl : RepoImpl) : Prop :=
  ∀ (n : Nat), 1 ≤ n →
    radList (impl.primefac.primefac n) ∣ n

/-- Radical is squarefree: for `n ≥ 1`, the factorization of the product of the
    distinct prime factors of `n` has no two equal adjacent entries. -/
def spec_primefac_radical_squarefree (impl : RepoImpl) : Prop :=
  ∀ (n : Nat), 1 ≤ n →
    hasNoAdjDup
        (impl.primefac.primefac (radList (impl.primefac.primefac n))) = true

/-- Radical is power-invariant: for `n ≥ 1` and `k ≥ 1`, the radical of `n ^ k`
    equals the radical of `n`. -/
def spec_primefac_radical_pow_invariant (impl : RepoImpl) : Prop :=
  ∀ (n k : Nat), 1 ≤ n → 1 ≤ k →
    radList (impl.primefac.primefac (powNat n k))
      = radList (impl.primefac.primefac n)

/-- Radical inclusion–exclusion: for `a, b ≥ 1`,
    `radList (primefac (a*b)) * radList (primefac (gcd a b))
      = radList (primefac a) * radList (primefac b)`. -/
def spec_primefac_radical_mul_gcd (impl : RepoImpl) : Prop :=
  ∀ (a b : Nat), 1 ≤ a → 1 ≤ b →
    radList (impl.primefac.primefac (a * b))
      * radList (impl.primefac.primefac (Nat.gcd a b))
      = radList (impl.primefac.primefac a)
        * radList (impl.primefac.primefac b)

/-- Squarefree ⇔ fixed by the radical: for `n ≥ 1`, `primefac n` has no equal
    adjacent entries exactly when the product of its distinct entries is `n`. -/
def spec_primefac_squarefree_iff_radical (impl : RepoImpl) : Prop :=
  ∀ (n : Nat), 1 ≤ n →
    (hasNoAdjDup (impl.primefac.primefac n) = true
      ↔ radList (impl.primefac.primefac n) = n)

/-- Divisor-count multiplicativity on coprimes: for `a, b ≥ 1` with
    `gcd a b = 1`, `divisorCount (a*b)` equals the product of the divisor-count
    product formulas of `a` and `b`. -/
def spec_primefac_tau_coprime_mul (impl : RepoImpl) : Prop :=
  ∀ (a b : Nat), 1 ≤ a → 1 ≤ b → Nat.gcd a b = 1 →
    divisorCount (a * b)
      = tauList (impl.primefac.primefac a)
        * tauList (impl.primefac.primefac b)

/-- Divisor-count parity ⇔ perfect square ⇔ all multiplicities even: for
    `n ≥ 1`, `divisorCount n` is odd exactly when `n` is a perfect square, and
    exactly when every prime factor of `n` occurs an even number of times. -/
def spec_primefac_tau_odd_iff_square (impl : RepoImpl) : Prop :=
  ∀ (n : Nat), 1 ≤ n →
    (divisorCount n % 2 = 1 ↔ ∃ r, r * r = n)
      ∧ (divisorCount n % 2 = 1 ↔
          ∀ p, p ∈ impl.primefac.primefac n →
            countList p (impl.primefac.primefac n) % 2 = 0)

/-- Perfect `k`-th power ⇔ all multiplicities divisible by `k`: for `n ≥ 1` and
    `k ≥ 2`, `n` is a `k`-th power exactly when every prime factor of `n` occurs
    a multiple-of-`k` number of times. -/
def spec_primefac_perfect_power_iff (impl : RepoImpl) : Prop :=
  ∀ (n k : Nat), 1 ≤ n → 2 ≤ k →
    ((∃ r, powNat r k = n) ↔
      ∀ p, p ∈ impl.primefac.primefac n →
        k ∣ countList p (impl.primefac.primefac n))

/-- Sum-of-divisors product formula: for `n ≥ 1`, `divisorSum n` equals the
    product over the distinct prime factors of `n` of the geometric factor
    `1 + p + ⋯ + p^eₚ`. -/
def spec_primefac_divisor_sum_product (impl : RepoImpl) : Prop :=
  ∀ (n : Nat), 1 ≤ n →
    divisorSum n
      = prodList ((impl.primefac.primefac n).eraseDups.map
          (fun p => geoFactor p (countList p (impl.primefac.primefac n))))
