import Rsa.Harness

/-!
# Rsa.Spec.Common

Specifications for the number-theoretic primitives `gcd`, `extendedGcd`,
`inverse`, and `crt`. Each `spec_*` is a property over an arbitrary
`impl : RepoImpl`; an API is always reached through `impl.rsa.<fn>`, never
by calling the reference `Rsa.<fn>` directly.

Each obligation characterises its output by a relation over `*`, `+`, `%`,
`∣`, `<`:

* `gcd` — the divisibility relation (divides both arguments; every common
  divisor divides it).
* `extendedGcd` — the Bézout identity `a*x + b*y = g` together with
  `g = gcd a b`.
* `inverse` — `(x * inv) % n = 1` together with `inv < n`.
* `crt` — the congruence law (the result reduces to each input residue
  modulo its modulus) together with the range clause `crt < ∏ moduli`.

A few concrete-vector specs anchor return values at fixed inputs.

DO NOT MODIFY — this file is frozen curator-given content.
-/

-- ════════════════════════════════════════════════════════════════
-- Frozen spec-side vocabulary
-- ════════════════════════════════════════════════════════════════

/-- Product of a list of moduli (the CRT modulus). This is the specification's
    own ground truth for the modulus product — it is intentionally NOT reached
    through `impl`, so the `crt` range and list-congruence obligations are pinned
    against a fixed reference rather than against whatever product the candidate
    implementation happens to form. Definitionally identical to the reference
    `listProd` used inside the `crt` implementation. -/
def listProdRef (ms : List Nat) : Nat :=
  ms.foldl (· * ·) 1

-- ════════════════════════════════════════════════════════════════
-- gcd: characterised by the frozen divisibility relation
-- ════════════════════════════════════════════════════════════════

/-- The gcd divides its first argument. -/
def spec_gcd_dvd_left (impl : RepoImpl) : Prop :=
  ∀ (a b : Nat), impl.rsa.gcd a b ∣ a

/-- The gcd divides its second argument. -/
def spec_gcd_dvd_right (impl : RepoImpl) : Prop :=
  ∀ (a b : Nat), impl.rsa.gcd a b ∣ b

/-- Maximality: every common divisor of `a` and `b` divides `gcd a b`. -/
def spec_gcd_greatest (impl : RepoImpl) : Prop :=
  ∀ (a b e : Nat), e ∣ a → e ∣ b → e ∣ impl.rsa.gcd a b

/-- Commutativity of gcd: `gcd a b = gcd b a`. -/
def spec_gcd_comm (impl : RepoImpl) : Prop :=
  ∀ (a b : Nat), impl.rsa.gcd a b = impl.rsa.gcd b a

/-- Right zero: `gcd a 0 = a`. -/
def spec_gcd_zero_right (impl : RepoImpl) : Prop :=
  ∀ (a : Nat), impl.rsa.gcd a 0 = a

/-- Concrete vector: `gcd 240 46 = 2`. -/
def spec_gcd_vec (impl : RepoImpl) : Prop :=
  impl.rsa.gcd 240 46 = 2

-- ════════════════════════════════════════════════════════════════
-- extendedGcd: Bézout identity + gcd agreement (frozen *, +, ∣)
-- ════════════════════════════════════════════════════════════════

/-- Bézout identity: the returned coefficients `(g, x, y)` satisfy
    `(a : Int) * x + (b : Int) * y = g`. -/
def spec_extended_gcd_bezout (impl : RepoImpl) : Prop :=
  ∀ (a b : Nat),
    (Int.ofNat a) * (impl.rsa.extendedGcd a b).2.1
      + (Int.ofNat b) * (impl.rsa.extendedGcd a b).2.2
      = Int.ofNat (impl.rsa.extendedGcd a b).1

/-- The gcd component of `extendedGcd` agrees with `gcd`: the first component
    of the Bézout triple is exactly `gcd a b`. -/
def spec_extended_gcd_fst (impl : RepoImpl) : Prop :=
  ∀ (a b : Nat), (impl.rsa.extendedGcd a b).1 = impl.rsa.gcd a b

/-- Concrete vector: `extendedGcd 240 46 = (2, -9, 47)`. -/
def spec_extended_gcd_vec1 (impl : RepoImpl) : Prop :=
  impl.rsa.extendedGcd 240 46 = (2, -9, 47)

/-- Concrete vector: `extendedGcd 6 4 = (2, 1, -1)`. -/
def spec_extended_gcd_vec2 (impl : RepoImpl) : Prop :=
  impl.rsa.extendedGcd 6 4 = (2, 1, -1)

-- ════════════════════════════════════════════════════════════════
-- inverse: the unique modular inverse (frozen *, %, < — `inv < n` mandatory)
-- ════════════════════════════════════════════════════════════════

/-- Modular-inverse correctness: when `gcd x n = 1` and `1 < n`, the residue
    `inv = inverse x n` satisfies both `(x * inv) % n = 1` and `inv < n`. -/
def spec_inverse_correct (impl : RepoImpl) : Prop :=
  ∀ (x n : Nat), impl.rsa.gcd x n = 1 → 1 < n →
    (x * impl.rsa.inverse x n) % n = 1 ∧ impl.rsa.inverse x n < n

/-- Range pin: `inverse x n < n` for every `n > 1`, regardless of
    coprimality. -/
def spec_inverse_lt (impl : RepoImpl) : Prop :=
  ∀ (x n : Nat), 1 < n → impl.rsa.inverse x n < n

/-- Existence under coprimality: when `gcd x n = 1` and `1 < n`, an inverse
    residue exists in `[0, n)` — there is some `inv < n` with
    `(x * inv) % n = 1`, and `inverse x n` is a witness. -/
def spec_inverse_exists (impl : RepoImpl) : Prop :=
  ∀ (x n : Nat), impl.rsa.gcd x n = 1 → 1 < n →
    ∃ inv, inv < n ∧ (x * inv) % n = 1 ∧ impl.rsa.inverse x n = inv

/-- Concrete vector: `inverse 3 11 = 4` (since `3 * 4 = 12 ≡ 1 mod 11`). -/
def spec_inverse_vec1 (impl : RepoImpl) : Prop :=
  impl.rsa.inverse 3 11 = 4

/-- Concrete vector: `inverse 17 3120 = 2753`. -/
def spec_inverse_vec2 (impl : RepoImpl) : Prop :=
  impl.rsa.inverse 17 3120 = 2753

-- ════════════════════════════════════════════════════════════════
-- crt: Chinese-Remainder congruence law + range (frozen %, *, <)
-- ════════════════════════════════════════════════════════════════

/-- Range clause: the CRT solution is reduced into `[0, ∏ moduli)` —
    `crt residues moduli < listProdRef moduli` whenever the modulus product is
    positive (`listProdRef` is the spec's own ground truth, not `impl`). -/
def spec_crt_range (impl : RepoImpl) : Prop :=
  ∀ (residues moduli : List Nat),
    0 < listProdRef moduli → impl.rsa.crt residues moduli < listProdRef moduli

/-- Single-modulus reduction: `crt [a] [m] = a % m` for `m > 0`. -/
def spec_crt_single (impl : RepoImpl) : Prop :=
  ∀ (a m : Nat), 0 < m → impl.rsa.crt [a] [m] = a % m

/-- Two-modulus congruence law: for coprime positive moduli `m₁`, `m₂`
    (`gcd m₁ m₂ = 1`), the CRT solution reduces to each input residue modulo
    its own modulus — `(crt [a₁,a₂] [m₁,m₂]) % m₁ = a₁ % m₁` and
    `… % m₂ = a₂ % m₂`. -/
def spec_crt_congruence_pair (impl : RepoImpl) : Prop :=
  ∀ (a₁ a₂ m₁ m₂ : Nat),
    0 < m₁ → 0 < m₂ → impl.rsa.gcd m₁ m₂ = 1 →
      (impl.rsa.crt [a₁, a₂] [m₁, m₂]) % m₁ = a₁ % m₁
        ∧ (impl.rsa.crt [a₁, a₂] [m₁, m₂]) % m₂ = a₂ % m₂

/-- Concrete vector: `crt [2,3] [3,5] = 8` (the `x ∈ [0,15)` with
    `x ≡ 2 mod 3` and `x ≡ 3 mod 5`). -/
def spec_crt_vec1 (impl : RepoImpl) : Prop :=
  impl.rsa.crt [2, 3] [3, 5] = 8

/-- Concrete vector: `crt [1,2,3] [2,3,5] = 23` (a three-modulus solution). -/
def spec_crt_vec2 (impl : RepoImpl) : Prop :=
  impl.rsa.crt [1, 2, 3] [2, 3, 5] = 23

-- ════════════════════════════════════════════════════════════════
-- Deeper end-facts
-- ════════════════════════════════════════════════════════════════

/-- Inverse of a modular power: when `gcd m n = 1` and `1 < n`, the reduced
    power `encryptInt m e n = (m^e) % n` is itself invertible, and `inverse`
    recovers its inverse residue —
    `(impl.rsa.encryptInt m e n * impl.rsa.inverse (impl.rsa.encryptInt m e n) n) % n = 1`. -/
def spec_inverse_of_power (impl : RepoImpl) : Prop :=
  ∀ (m e n : Nat), impl.rsa.gcd m n = 1 → 1 < n →
    (impl.rsa.encryptInt m e n * impl.rsa.inverse (impl.rsa.encryptInt m e n) n) % n = 1

/-- Uniqueness of the CRT solution: for coprime positive moduli `m₁`, `m₂`,
    the CRT output is the only value in `[0, m₁*m₂)` simultaneously congruent
    (modulo each modulus) to the corresponding input residue — any
    `y < m₁*m₂` whose residues match those of `crt [a₁,a₂] [m₁,m₂]` must
    equal it. -/
def spec_crt_unique (impl : RepoImpl) : Prop :=
  ∀ (a₁ a₂ m₁ m₂ y : Nat),
    0 < m₁ → 0 < m₂ → impl.rsa.gcd m₁ m₂ = 1 →
    y < m₁ * m₂ →
    y % m₁ = (impl.rsa.crt [a₁, a₂] [m₁, m₂]) % m₁ →
    y % m₂ = (impl.rsa.crt [a₁, a₂] [m₁, m₂]) % m₂ →
    y = impl.rsa.crt [a₁, a₂] [m₁, m₂]

/-- General list-CRT head congruence: for an arbitrary-length modulus list
    `m :: ms` whose head `m > 1`, whose tail moduli are all positive, and
    whose head is coprime to the product of the tail
    (`gcd (listProdRef ms) m = 1`, tying `crt` to the `gcd` API and to the spec's
    own `listProdRef` ground truth), the CRT solution reduces to the head residue
    — `(crt (a :: as) (m :: ms)) % m = a % m`. -/
def spec_crt_congruence_list (impl : RepoImpl) : Prop :=
  ∀ (a : Nat) (as : List Nat) (m : Nat) (ms : List Nat),
    1 < m → (∀ mj ∈ ms, 0 < mj) → impl.rsa.gcd (listProdRef ms) m = 1 →
      (impl.rsa.crt (a :: as) (m :: ms)) % m = a % m

/-- Euclidean recurrence of `extendedGcd`: for `b > 0`, one step relates
    `extendedGcd a b` to the sub-call on `(b, a % b)` — the divisor is
    unchanged, the returned `x` is the sub-call's `y`, and the returned `y` is
    `x' - (a / b) * y'` (over integer `-`, `*`, `Int.ofNat`, and `Nat` `/`,
    `%`). This pins the recursive structure of the coefficient computation,
    not merely the Bézout identity the coefficients satisfy. -/
def spec_extended_gcd_recurrence (impl : RepoImpl) : Prop :=
  ∀ (a b : Nat), 0 < b →
    impl.rsa.extendedGcd a b
      = ((impl.rsa.extendedGcd b (a % b)).1,
         (impl.rsa.extendedGcd b (a % b)).2.2,
         (impl.rsa.extendedGcd b (a % b)).2.1
           - (Int.ofNat (a / b)) * (impl.rsa.extendedGcd b (a % b)).2.2)

/-- The modular inverse is the only residue below `n` whose product with `x`
    reduces to `1`. -/
def spec_inverse_unique_residue (impl : RepoImpl) : Prop :=
  ∀ (x n y : Nat), impl.rsa.gcd x n = 1 → 1 < n → y < n →
    (x * y) % n = 1 → y = impl.rsa.inverse x n

/-- Applying modular inverse twice returns the original residue modulo `n`. -/
def spec_inverse_involution (impl : RepoImpl) : Prop :=
  ∀ (x n : Nat), impl.rsa.gcd x n = 1 → 1 < n →
    impl.rsa.inverse (impl.rsa.inverse x n) n = x % n

def divisorList (n : Nat) : List Nat :=
  (List.range (n + 1)).filter (fun d => decide (d ∣ n))

def gcdClassCount (impl : RepoImpl) (n d : Nat) : Nat :=
  ((List.range n).filter (fun x => impl.rsa.gcd x n == d)).length

/-- Summing, over the divisors of `n`, the count of `x < n` with
    `gcd x n = d`, recovers `n`. -/
def spec_gcd_class_partition_count (impl : RepoImpl) : Prop :=
  ∀ (n : Nat),
    (divisorList n).foldl (fun acc d => acc + gcdClassCount impl n d) 0 = n

def crtPairTable (impl : RepoImpl) (m n : Nat) : List Nat :=
  (List.range m).flatMap (fun a =>
    (List.range n).map (fun b => impl.rsa.crt [a, b] [m, n]))

/-- The CRT pair-table over `[0,m)×[0,n)` is a permutation of `[0,m*n)`. -/
def spec_crt_pair_permutes_range (impl : RepoImpl) : Prop :=
  ∀ (m n : Nat), 0 < m → 0 < n → impl.rsa.gcd m n = 1 →
    List.Perm (crtPairTable impl m n) (List.range (m * n))

def unitCount (impl : RepoImpl) (n : Nat) : Nat :=
  ((List.range n).filter (fun x => impl.rsa.gcd x n == 1)).length

/-- For coprime `m,n`, the count of units mod `m*n` is the product of the
    unit counts. -/
def spec_coprime_count_mul (impl : RepoImpl) : Prop :=
  ∀ (m n : Nat), impl.rsa.gcd m n = 1 →
    unitCount impl (m * n) = unitCount impl m * unitCount impl n

def firstIndexOf (x : Nat) : List Nat → Nat
  | [] => 0
  | y :: ys => if y == x then 0 else firstIndexOf x ys + 1

/-- The row-major first index of `y` in the CRT pair-table is `(y%m)*n + y%n`. -/
def spec_crt_pair_first_index (impl : RepoImpl) : Prop :=
  ∀ (m n y : Nat), 0 < m → 0 < n → impl.rsa.gcd m n = 1 → y < m * n →
    firstIndexOf y (crtPairTable impl m n) = (y % m) * n + (y % n)
-- ════════════════════════════════════════════════════════════════
-- Non-coprime CRT, unit-group structure, and deeper counting laws
-- ════════════════════════════════════════════════════════════════

def unitResidues (impl : RepoImpl) (n : Nat) : List Nat :=
  (List.range n).filter (fun x => impl.rsa.gcd x n == 1)

def inverseUnitResidues (impl : RepoImpl) (n : Nat) : List Nat :=
  (unitResidues impl n).map (fun x => impl.rsa.inverse x n)

def projectedUnitCard (impl : RepoImpl) (m n : Nat) : Nat :=
  ((List.range (m * n)).filter (fun y =>
    (impl.rsa.gcd (y % m) m == 1) && (impl.rsa.gcd (y % n) n == 1))).length

def crtTripleTable (impl : RepoImpl) (m n k : Nat) : List Nat :=
  (List.range m).flatMap (fun a =>
    (List.range n).flatMap (fun b =>
      (List.range k).map (fun c => impl.rsa.crt [a, b, c] [m, n, k])))

/-- Non-coprime pair CRT: when the two moduli share a factor `d = gcd m n > 1`,
    the solution reduces modulo each modulus to its residue scaled by `d` —
    `(crt [a,b] [m,n]) % m = ((a % m) * d) % m` and `… % n = ((b % n) * d) % n`. -/
def spec_crt_pair_shared_factor_scaled_congruence (impl : RepoImpl) : Prop :=
  ∀ (a b m n : Nat), 0 < m → 0 < n →
    let d := impl.rsa.gcd m n
    1 < d →
      (impl.rsa.crt [a, b] [m, n]) % m = ((a % m) * d) % m
        ∧ (impl.rsa.crt [a, b] [m, n]) % n = ((b % n) * d) % n

/-- Non-coprime list-head CRT: when the head modulus `m` shares a factor with
    the tail-modulus product (`gcd (listProdRef ms) m > 1`), the solution
    reduces modulo `m` to the head residue scaled by that shared factor —
    `(crt (a :: as) (m :: ms)) % m = ((a % m) * (gcd (listProdRef ms) m % m)) % m`. -/
def spec_crt_non_coprime_head_scaled (impl : RepoImpl) : Prop :=
  ∀ (a : Nat) (as : List Nat) (m : Nat) (ms : List Nat),
    0 < m → (∀ mj ∈ ms, 0 < mj) → 1 < impl.rsa.gcd (listProdRef ms) m →
      (impl.rsa.crt (a :: as) (m :: ms)) % m =
        ((a % m) * (impl.rsa.gcd (listProdRef ms) m % m)) % m

/-- Modular inverse permutes the units: mapping `inverse · n` over the units
    below `n` yields a permutation of the same unit list. -/
def spec_inverse_units_permutes (impl : RepoImpl) : Prop :=
  ∀ (n : Nat), 1 < n →
    List.Perm (inverseUnitResidues impl n) (unitResidues impl n)

/-- Multiplicativity of the modular inverse over units: for units `x`, `y`
    modulo `n`, `inverse ((x * y) % n) n = (inverse x n * inverse y n) % n`. -/
def spec_inverse_mul_units (impl : RepoImpl) : Prop :=
  ∀ (x y n : Nat), 1 < n → impl.rsa.gcd x n = 1 → impl.rsa.gcd y n = 1 →
    impl.rsa.inverse ((x * y) % n) n =
      (impl.rsa.inverse x n * impl.rsa.inverse y n) % n

/-- The inverse of a unit occupies, in the mapped inverse list, the same
    position the unit occupies in the unit list —
    `firstIndexOf (inverse x n) (inverseUnitResidues impl n)
      = firstIndexOf x (unitResidues impl n)`. -/
def spec_inverse_unit_table_first_index (impl : RepoImpl) : Prop :=
  ∀ (x n : Nat), 1 < n → x < n → impl.rsa.gcd x n = 1 →
    firstIndexOf (impl.rsa.inverse x n) (inverseUnitResidues impl n) =
      firstIndexOf x (unitResidues impl n)

/-- CRT coordinate recovery: for coprime positive `m`, `n` and `y < m*n`,
    recombining `y`'s two residues returns `y` —
    `crt [y % m, y % n] [m, n] = y`. -/
def spec_crt_pair_roundtrip_residues (impl : RepoImpl) : Prop :=
  ∀ (m n y : Nat), 0 < m → 0 < n → impl.rsa.gcd m n = 1 → y < m * n →
    impl.rsa.crt [y % m, y % n] [m, n] = y

/-- Row-major CRT residue grid: mapping each CRT pair-table entry to its
    residue pair recovers the row-major `[0,m) × [0,n)` grid —
    `(crtPairTable impl m n).map (fun y => (y % m, y % n))
      = (List.range m).flatMap (fun a => (List.range n).map (fun b => (a, b)))`. -/
def spec_crt_pair_table_residue_pairs (impl : RepoImpl) : Prop :=
  ∀ (m n : Nat), 0 < m → 0 < n → impl.rsa.gcd m n = 1 →
    (crtPairTable impl m n).map (fun y => (y % m, y % n)) =
      (List.range m).flatMap (fun a => (List.range n).map (fun b => (a, b)))

/-- The three-modulus CRT table over pairwise-coprime positive moduli is a
    permutation of `[0, m*n*k)`. -/
def spec_crt_triple_table_permutes_range (impl : RepoImpl) : Prop :=
  ∀ (m n k : Nat), 0 < m → 0 < n → 0 < k →
    impl.rsa.gcd m n = 1 → impl.rsa.gcd (m * n) k = 1 →
      List.Perm (crtTripleTable impl m n k) (List.range (m * n * k))

/-- Units modulo a coprime product split coordinatewise: the count of `y < m*n`
    whose two projections `y % m`, `y % n` are units equals `unitCount m * unitCount n`. -/
def spec_unit_product_projection_cardinality (impl : RepoImpl) : Prop :=
  ∀ (m n : Nat), 0 < m → 0 < n → impl.rsa.gcd m n = 1 →
    projectedUnitCard impl m n = unitCount impl m * unitCount impl n

/-- Scaling law of `extendedGcd`: multiplying both inputs by `k > 0` multiplies
    the gcd component by `k` and leaves both Bézout coefficients unchanged —
    `extendedGcd (k*a) (k*b) = (k * g, x, y)` where `(g,x,y) = extendedGcd a b`. -/
def spec_extended_gcd_common_factor (impl : RepoImpl) : Prop :=
  ∀ (k a b : Nat), 0 < k →
    let r := impl.rsa.extendedGcd a b
    impl.rsa.extendedGcd (k * a) (k * b) = (k * r.1, r.2.1, r.2.2)

/-- Reduced-range bound on the Bézout coefficients: when `2 * gcd a b` is below
    both `a` and `b`, the coefficients scaled by `2 * gcd a b` stay strictly
    inside `(-b, b)` and `(-a, a)` respectively. -/
def spec_extended_gcd_scaled_half_bounds (impl : RepoImpl) : Prop :=
  ∀ (a b : Nat),
    let g := impl.rsa.gcd a b
    let r := impl.rsa.extendedGcd a b
    2 * g < a → 2 * g < b →
      -(Int.ofNat b) < Int.ofNat (2 * g) * r.2.1
        ∧ Int.ofNat (2 * g) * r.2.1 < Int.ofNat b
        ∧ -(Int.ofNat a) < Int.ofNat (2 * g) * r.2.2
        ∧ Int.ofNat (2 * g) * r.2.2 < Int.ofNat a

/-- Divisor-sum of unit counts: summing `unitCount d` over the divisors of `n`
    recovers `n` — `(divisorList n).foldl (fun acc d => acc + unitCount impl d) 0 = n`. -/
def spec_totient_divisor_sum (impl : RepoImpl) : Prop :=
  ∀ (n : Nat), 0 < n →
    (divisorList n).foldl (fun acc d => acc + unitCount impl d) 0 = n

/-- gcd-class cardinality via the quotient: for `n = d * q`, the number of
    `x < n` with `gcd x n = d` equals the number of units below `q` —
    `gcdClassCount impl n d = unitCount impl q`. -/
def spec_gcd_class_count_quotient (impl : RepoImpl) : Prop :=
  ∀ (n d q : Nat), 0 < d → d * q = n →
    gcdClassCount impl n d = unitCount impl q

-- ════════════════════════════════════════════════════════════════
-- Unit-group exponent laws + multiplicative order
-- ════════════════════════════════════════════════════════════════

/-- The positive exponents `k ≤ unitCount impl n` at which the modular power of
    `x` collapses to `1` — `encryptInt x k n = 1`. -/
def orderExponents (impl : RepoImpl) (x n : Nat) : List Nat :=
  (List.range (unitCount impl n + 1)).filter
    (fun k => decide (0 < k ∧ impl.rsa.encryptInt x k n = 1))

/-- The least positive exponent at which the modular power of `x` returns `1`
    (or `0` when no such exponent is found below `unitCount impl n`). -/
def multOrder (impl : RepoImpl) (x n : Nat) : Nat :=
  match orderExponents impl x n with
  | [] => 0
  | k :: _ => k

/-- For a unit `x` modulo `n` (`gcd x n = 1`, `1 < n`), raising `x` to the power
    `unitCount impl n` returns `1` —
    `encryptInt x (unitCount impl n) n = 1`. -/
def spec_unit_power_unitcount_one (impl : RepoImpl) : Prop :=
  ∀ (x n : Nat), 1 < n → impl.rsa.gcd x n = 1 →
    impl.rsa.encryptInt x (unitCount impl n) n = 1

/-- For a unit `x` modulo `n`, any exponent of the shape
    `k * unitCount impl n + 1` returns the reduced base —
    `encryptInt x (k * unitCount impl n + 1) n = x % n`. -/
def spec_unit_power_unitcount_cycle (impl : RepoImpl) : Prop :=
  ∀ (x k n : Nat), 1 < n → impl.rsa.gcd x n = 1 →
    impl.rsa.encryptInt x (k * unitCount impl n + 1) n = x % n

/-- For a unit `x` modulo `n`, the modular inverse equals the modular power of
    `x` by `unitCount impl n - 1` —
    `inverse x n = encryptInt x (unitCount impl n - 1) n`. -/
def spec_inverse_as_unitcount_power (impl : RepoImpl) : Prop :=
  ∀ (x n : Nat), 1 < n → impl.rsa.gcd x n = 1 →
    impl.rsa.inverse x n = impl.rsa.encryptInt x (unitCount impl n - 1) n

/-- For a unit `x` modulo `n`, the least positive exponent `ord = multOrder`
    returning `1` is positive, divides `unitCount impl n`, and returns `1` —
    `0 < ord ∧ ord ∣ unitCount impl n ∧ encryptInt x ord n = 1`. -/
def spec_mult_order_divides_unitcount (impl : RepoImpl) : Prop :=
  ∀ (x n : Nat), 1 < n → impl.rsa.gcd x n = 1 →
    0 < multOrder impl x n
      ∧ multOrder impl x n ∣ unitCount impl n
      ∧ impl.rsa.encryptInt x (multOrder impl x n) n = 1

/-- For a unit `x` modulo `n`, every positive exponent `k` with
    `encryptInt x k n = 1` is a multiple of `multOrder impl x n` —
    `multOrder impl x n ∣ k`. -/
def spec_mult_order_divides_periods (impl : RepoImpl) : Prop :=
  ∀ (x n k : Nat), 1 < n → impl.rsa.gcd x n = 1 →
    0 < k → impl.rsa.encryptInt x k n = 1 →
      multOrder impl x n ∣ k

-- ════════════════════════════════════════════════════════════════
-- Unit count of a prime power + full-residue round-trip + CRT product law
-- ════════════════════════════════════════════════════════════════

/-- `p` is prime: `1 < p` and every divisor of `p` is `1` or `p`. This is the
    specification's own ground truth for primality. -/
def specPrime (p : Nat) : Prop :=
  1 < p ∧ ∀ d : Nat, d ∣ p → d = 1 ∨ d = p

/-- The unit count of a prime power factors as `(p - 1) * p^(k-1)` —
    `unitCount impl (p ^ k) = (p - 1) * p ^ (k - 1)` for prime `p` and `k > 0`. -/
def spec_unitcount_prime_power (impl : RepoImpl) : Prop :=
  ∀ (p k : Nat), specPrime p → 0 < k →
    unitCount impl (p ^ k) = (p - 1) * p ^ (k - 1)

/-- Full-residue round-trip for a two-distinct-prime modulus: when
    `(e * d) % unitCount impl (p * q) = 1`, decryption inverts encryption on
    every residue below `p * q` (not merely the units) —
    `decryptInt (encryptInt m e (p*q)) d (p*q) = m` for all `m < p * q`. -/
def spec_full_residue_roundtrip_prime_product (impl : RepoImpl) : Prop :=
  ∀ (m e d p q : Nat),
    specPrime p → specPrime q → p ≠ q →
    (e * d) % unitCount impl (p * q) = 1 →
    m < p * q →
      impl.rsa.decryptInt (impl.rsa.encryptInt m e (p * q)) d (p * q) = m

/-- The CRT recombination carries products to products: for coprime positive
    `m`, `n`, recombining the coordinatewise products equals the reduced product
    of the recombinations —
    `crt [(a₁*a₂)%m, (b₁*b₂)%n] [m,n] = (crt [a₁,b₁] [m,n] * crt [a₂,b₂] [m,n]) % (m*n)`. -/
def spec_crt_pair_mul_hom (impl : RepoImpl) : Prop :=
  ∀ (a₁ b₁ a₂ b₂ m n : Nat),
    0 < m → 0 < n → impl.rsa.gcd m n = 1 →
      impl.rsa.crt [(a₁ * a₂) % m, (b₁ * b₂) % n] [m, n] =
        (impl.rsa.crt [a₁, b₁] [m, n] * impl.rsa.crt [a₂, b₂] [m, n]) % (m * n)
