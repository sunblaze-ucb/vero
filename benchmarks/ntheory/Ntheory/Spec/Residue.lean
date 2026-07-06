import Ntheory.Harness

/-!
# Ntheory.Spec.Residue

Specifications for the residue-number-theory operations. Each `spec_*` is a
property over an arbitrary `impl : RepoImpl`; an API is always reached
through `impl.ntheory.<fn>`. Every output is characterized by an algebraic
relation against Lean's `^`, `%`, `*`, `∣`, `≤`, `<`, and `Nat.gcd` over an
unbounded numeric domain.

The existence-bearing APIs `sqrtMod`, `nthrootMod`, and `discreteLog` each
carry a soundness clause (a returned root / exponent satisfies the defining
congruence), a least clause (no smaller residue / exponent works), and a
completeness clause (a returned `none` certifies that no witness exists).

The Jacobi symbol is pinned by its base case, denominator-`1` value,
numerator periodicity mod `n`, value range, and agreement with the Legendre
symbol at odd primes. The totient is pinned by frozen `Nat.gcd` as a unit
count (base value, bounds, positivity, the value `p-1` at a prime) plus the
divisor-sum identity `∑_{d ∣ n} totient(d) = n`, stated against the frozen
`divisorsOf` enumeration.

A final block states multiplicative-order / discrete-log / square-root laws
relating these APIs to `^`, `%`, `∣`, `≤`, `<`.

DO NOT MODIFY — this file is frozen.
-/

-- ── Frozen ground-truth machinery (DO NOT MODIFY) ──────────────

/-- `divisorsOf n`: the ascending list of positive divisors of `n` — every
    `d` in `[1, n]` with `n % d = 0`. The specification's own ground truth for
    ranging over divisors; it never refers to `impl`. -/
def divisorsOf (n : Nat) : List Nat :=
  (List.range (n + 1)).filter (fun d => d != 0 && n % d == 0)

/-- `intResidue a n`: the canonical residue in `[0, n)` of a signed integer
    numerator — `(a % n).toNat`. The specification's own reduction of a signed
    Jacobi numerator; it never refers to `impl`. -/
def intResidue (a : Int) (n : Nat) : Nat :=
  (a % (n : Int)).toNat

/-- `isPrimeCert p`: the frozen primality certificate — `p ≥ 2` with no divisor
    `d` in the open interval `(1, p)`. Used to quantify laws over the unbounded
    prime family without any appeal to `impl`. -/
def isPrimeCert (p : Nat) : Prop :=
  2 ≤ p ∧ ∀ d, 1 < d → d < p → ¬ (d ∣ p)

-- ════════════════════════════════════════════════════════════════
-- Quadratic residue / Legendre symbol
--
-- Quadratic residuosity is pinned by a FROZEN existential over the
-- complete residue system `x < p`: `a` is a (nonzero) quadratic residue
-- iff some `x` squares to `a` mod `p`. The Legendre symbol is then pinned
-- to `{-1, 0, 1}` by three mutually-exclusive iff's, the `-1` case carrying
-- the no-witness completeness half.
-- ════════════════════════════════════════════════════════════════

/-- Quadratic-residue characterization (frozen existential, both halves):
    `isQuadraticResidue a p` is `true` exactly when `a` is nonzero mod `p`
    *and* some residue `x < p` squares to `a` mod `p`. The forward direction
    is soundness (a `true` is backed by a concrete square root); the reverse
    is completeness (any genuine square root forces `true`). Anchored on
    frozen `*`/`%` with an unbounded `a`; a degenerate constant predicate
    fails one direction. -/
def spec_qr_iff (impl : RepoImpl) : Prop :=
  ∀ (a p : Nat),
    impl.ntheory.isQuadraticResidue a p = true ↔
      (a % p ≠ 0 ∧ ∃ x, x < p ∧ (x * x) % p = a % p)

/-- Legendre zero case: `legendreSymbol a p = 0` exactly when `p ∣ a`
    (`a % p = 0`). Pins the symbol's vanishing to genuine divisibility. -/
def spec_legendre_zero_iff (impl : RepoImpl) : Prop :=
  ∀ (a p : Nat),
    impl.ntheory.legendreSymbol a p = 0 ↔ a % p = 0

/-- Legendre `+1` case: `legendreSymbol a p = 1` exactly when `a` is a
    nonzero quadratic residue. Ties the two residue APIs together so the
    symbol's `+1` value is pinned to genuine residuosity. -/
def spec_legendre_one_iff (impl : RepoImpl) : Prop :=
  ∀ (a p : Nat),
    impl.ntheory.legendreSymbol a p = 1 ↔ impl.ntheory.isQuadraticResidue a p = true

/-- Legendre `-1` case (completeness half): `legendreSymbol a p = -1`
    exactly when `a` is nonzero mod `p` yet *no* residue `x < p` squares to
    it — the genuine non-residue certificate. This is the no-witness
    completeness clause: it forbids reporting `-1` whenever a square root
    actually exists, and forbids `-1` for `a ≡ 0`. -/
def spec_legendre_neg_one_iff (impl : RepoImpl) : Prop :=
  ∀ (a p : Nat),
    impl.ntheory.legendreSymbol a p = -1 ↔
      (a % p ≠ 0 ∧ ∀ x, x < p → (x * x) % p ≠ a % p)

/-- Legendre range: the symbol is always one of `-1`, `0`, `1`. Closes the
    value channel so no out-of-range symbol can be reported. -/
def spec_legendre_range (impl : RepoImpl) : Prop :=
  ∀ (a p : Nat),
    impl.ntheory.legendreSymbol a p = -1 ∨
    impl.ntheory.legendreSymbol a p = 0 ∨
    impl.ntheory.legendreSymbol a p = 1

-- ════════════════════════════════════════════════════════════════
-- Jacobi symbol — pinned by its characterizing laws: base case
-- `(a/1) = 1`, empty denominator `(a/0) = 0`, numerator periodicity mod `n`,
-- value range, agreement with Legendre at odd primes, and worked values.
-- ════════════════════════════════════════════════════════════════

/-- Jacobi base case: `(a / 1) = 1` for every numerator. The recurrence's
    terminal value, pinned for all `a`. -/
def spec_jacobi_base (impl : RepoImpl) : Prop :=
  ∀ (a : Int), impl.ntheory.jacobiSymbol a 1 = 1

/-- Jacobi numerator periodicity (a recurrence law): the symbol depends on
    the numerator only mod `n` — `(a / n) = ((a + n) / n)` for every `a` and
    `n`. A universal law no finite lookup table can fake. -/
def spec_jacobi_periodic (impl : RepoImpl) : Prop :=
  ∀ (a : Int) (n : Nat),
    impl.ntheory.jacobiSymbol a n = impl.ntheory.jacobiSymbol (a + (n : Int)) n

/-- Jacobi range: `(a / n) ∈ {-1, 0, 1}` for every `a`, `n`. Closes the
    symbol's value channel. -/
def spec_jacobi_range (impl : RepoImpl) : Prop :=
  ∀ (a : Int) (n : Nat),
    impl.ntheory.jacobiSymbol a n = -1 ∨
    impl.ntheory.jacobiSymbol a n = 0 ∨
    impl.ntheory.jacobiSymbol a n = 1

/-- Jacobi agrees with Legendre at odd primes (reciprocity check-points):
    on a fixed table of odd-prime denominators the Jacobi symbol equals the
    Legendre symbol at every residue, forcing the recurrence's value to line
    up with genuine quadratic residuosity (not just the structural laws). -/
def spec_jacobi_matches_legendre (impl : RepoImpl) : Prop :=
  (∀ a : Nat, a < 7 → impl.ntheory.jacobiSymbol (a : Int) 7 = impl.ntheory.legendreSymbol a 7) ∧
  (∀ a : Nat, a < 11 → impl.ntheory.jacobiSymbol (a : Int) 11 = impl.ntheory.legendreSymbol a 11)

/-- Jacobi reciprocity worked values (concrete anchors against frozen
    constants): the symbol takes its standard value at non-trivial
    composite and large-prime arguments — `(2/15) = 1`, `(7/15) = -1`,
    `(5/21) = 1`, `(6/9) = 0` (a shared factor), and the classic
    `(1001/9907) = -1`. These force a real reciprocity computation. -/
def spec_jacobi_values (impl : RepoImpl) : Prop :=
  impl.ntheory.jacobiSymbol 2 15 = 1 ∧
  impl.ntheory.jacobiSymbol 7 15 = -1 ∧
  impl.ntheory.jacobiSymbol 5 21 = 1 ∧
  impl.ntheory.jacobiSymbol 6 9 = 0 ∧
  impl.ntheory.jacobiSymbol 1001 9907 = -1

-- ════════════════════════════════════════════════════════════════
-- sqrtMod — witness ∧ least ∧ completeness of the canonical square root.
-- ════════════════════════════════════════════════════════════════

/-- `sqrtMod` soundness (witness): a returned root `r` is a genuine square
    root in range — `(r*r) ≡ a (mod p)` and `r < p`. Frozen-op-anchored on
    `*`/`%`; rules out a fabricated root. -/
def spec_sqrt_mod_sound (impl : RepoImpl) : Prop :=
  ∀ (a p r : Nat),
    impl.ntheory.sqrtMod a p = some r → (r * r) % p = a % p ∧ r < p

/-- `sqrtMod` least (canonical representative, uniqueness): the returned
    root is the *least* residue that squares to `a` — no smaller `y < r`
    works. Pins the answer to the unique canonical root, so two correct
    impls must agree on it. -/
def spec_sqrt_mod_least (impl : RepoImpl) : Prop :=
  ∀ (a p r : Nat),
    impl.ntheory.sqrtMod a p = some r → ∀ y, y < r → (y * y) % p ≠ a % p

/-- `sqrtMod` completeness (the mandatory `none` certificate): a returned
    `none` proves *no* residue `x < p` squares to `a`. Without this clause
    the soundness clause alone is satisfied by `fun _ _ => none`. -/
def spec_sqrt_mod_complete (impl : RepoImpl) : Prop :=
  ∀ (a p : Nat),
    impl.ntheory.sqrtMod a p = none → ∀ x, x < p → (x * x) % p ≠ a % p

/-- `sqrtMod` existence iff a root exists (decision tie): `sqrtMod a p`
    succeeds exactly when some residue `x < p` squares to `a`. The combined
    decision form of soundness + completeness. -/
def spec_sqrt_mod_isSome_iff (impl : RepoImpl) : Prop :=
  ∀ (a p : Nat),
    (impl.ntheory.sqrtMod a p).isSome = true ↔ ∃ x, x < p ∧ (x * x) % p = a % p

-- ════════════════════════════════════════════════════════════════
-- nthrootMod — witness ∧ least ∧ completeness of the canonical k-th root.
-- ════════════════════════════════════════════════════════════════

/-- `nthrootMod` soundness (witness): a returned root `r` genuinely satisfies
    `r^k ≡ a (mod p)` with `r < p`. Frozen-op-anchored on `^`/`%`. -/
def spec_nthroot_mod_sound (impl : RepoImpl) : Prop :=
  ∀ (a k p r : Nat),
    impl.ntheory.nthrootMod a k p = some r → (r ^ k) % p = a % p ∧ r < p

/-- `nthrootMod` least (canonical representative): the returned `k`-th root
    is the least residue with `r^k ≡ a` — no smaller `y < r` works. -/
def spec_nthroot_mod_least (impl : RepoImpl) : Prop :=
  ∀ (a k p r : Nat),
    impl.ntheory.nthrootMod a k p = some r → ∀ y, y < r → (y ^ k) % p ≠ a % p

/-- `nthrootMod` completeness (the mandatory `none` certificate): a returned
    `none` proves no residue `x < p` is a `k`-th root of `a`. -/
def spec_nthroot_mod_complete (impl : RepoImpl) : Prop :=
  ∀ (a k p : Nat),
    impl.ntheory.nthrootMod a k p = none → ∀ x, x < p → (x ^ k) % p ≠ a % p

-- ════════════════════════════════════════════════════════════════
-- discreteLog — soundness ∧ least ∧ completeness of the least exponent.
-- ════════════════════════════════════════════════════════════════

/-- `discreteLog` soundness: a returned exponent `x` genuinely solves the
    congruence — `b^x ≡ a (mod n)`. Frozen-op-anchored on `^`/`%`. -/
def spec_discrete_log_sound (impl : RepoImpl) : Prop :=
  ∀ (n a b x : Nat),
    impl.ntheory.discreteLog n a b = some x → (b ^ x) % n = a % n

/-- `discreteLog` least exponent (uniqueness): the returned exponent is the
    *least* solution — no smaller `y < x` solves the congruence. Pins the
    answer to the canonical least discrete log. -/
def spec_discrete_log_least (impl : RepoImpl) : Prop :=
  ∀ (n a b x : Nat),
    impl.ntheory.discreteLog n a b = some x → ∀ y, y < x → (b ^ y) % n ≠ a % n

/-- `discreteLog` completeness (the explicit anti-vacuity fix): a returned
    `none` certifies that *no* exponent `x < n` solves `b^x ≡ a (mod n)` —
    `n` exhausts a full multiplicative period, so this forbids the
    degenerate `fun _ _ _ => none` that satisfies soundness vacuously. -/
def spec_discrete_log_complete (impl : RepoImpl) : Prop :=
  ∀ (n a b : Nat),
    impl.ntheory.discreteLog n a b = none → ∀ x, x < n → (b ^ x) % n ≠ a % n

-- ════════════════════════════════════════════════════════════════
-- nOrder — least-positive-period characterization (paired witness + least).
-- ════════════════════════════════════════════════════════════════

/-- `nOrder` period (witness): whenever `nOrder a n` is a found order (the
    non-sentinel `0 < k` case), `a` raised to it is `1` mod `n` —
    `a^(nOrder a n) ≡ 1 (mod n)`. Frozen-op-anchored on `^`/`%`. -/
def spec_n_order_period (impl : RepoImpl) : Prop :=
  ∀ (a n : Nat),
    0 < impl.ntheory.nOrder a n →
      (a ^ (impl.ntheory.nOrder a n)) % n = 1 % n

/-- `nOrder` least positive period (uniqueness): the found order is the
    *least* positive exponent with `a^k ≡ 1` — no `0 < j < nOrder a n`
    works. Together with `spec_n_order_period` this pins the multiplicative
    order to its unique least value. -/
def spec_n_order_least (impl : RepoImpl) : Prop :=
  ∀ (a n j : Nat),
    0 < impl.ntheory.nOrder a n →
      0 < j → j < impl.ntheory.nOrder a n → (a ^ j) % n ≠ 1 % n

/-- `nOrder` completeness (the explicit anti-vacuity fix): if *any* positive
    exponent `k < n` returns `a` to `1` mod `n`, then `nOrder a n` is positive
    (a real order was found, not the `0` sentinel). Every preceding `nOrder`
    law is guarded by `0 < nOrder a n`, so without this clause the degenerate
    `fun _ _ => 0` satisfies them all vacuously. This forbids it: whenever a
    period exists in `[1, n)`, the impl must report a found order. -/
def spec_n_order_complete (impl : RepoImpl) : Prop :=
  ∀ (a n k : Nat),
    0 < k → k < n → (a ^ k) % n = 1 % n →
      0 < impl.ntheory.nOrder a n

-- ════════════════════════════════════════════════════════════════
-- totient — frozen `Nat.gcd` unit-count characterization: base value,
-- bounds, positivity, value at a prime, and the divisor-sum identity.
-- ════════════════════════════════════════════════════════════════

/-- Totient anchor: `totient 1 = 1`. The base value of the unit count. -/
def spec_totient_one (impl : RepoImpl) : Prop :=
  impl.ntheory.totient 1 = 1

/-- Totient upper bound: `totient n ≤ n` — at most every residue is a unit.
    Frozen-op `≤` over unbounded `n`. -/
def spec_totient_le (impl : RepoImpl) : Prop :=
  ∀ (n : Nat), impl.ntheory.totient n ≤ n

/-- Totient positivity: every `n ≥ 1` has at least one unit (namely `1`
    itself), so `1 ≤ totient n`. Rules out the degenerate `totient ≡ 0`. -/
def spec_totient_pos (impl : RepoImpl) : Prop :=
  ∀ (n : Nat), 1 ≤ n → 1 ≤ impl.ntheory.totient n

/-- Totient at a prime (frozen-divisibility-anchored, forces real counting):
    if `p ≥ 2` has no divisor `d` with `1 < d < p` (a primality certificate
    stated against frozen `∣`), then `totient p = p - 1` — every nonzero
    residue is a unit. A degenerate or constant `totient` fails this. -/
def spec_totient_prime (impl : RepoImpl) : Prop :=
  ∀ (p : Nat),
    2 ≤ p → (∀ d, 1 < d → d < p → ¬ (d ∣ p)) →
      impl.ntheory.totient p = p - 1

/-- Totient STRICT upper bound: `totient n < n` for every `n ≥ 2` — at least
    `n` itself (`gcd n n = n ≠ 1`) is a non-unit, so the count is strictly
    below `n`. Strictly stronger than `spec_totient_le` on the composite range
    a `totient ≡ n` impl would otherwise satisfy; forces genuine exclusion
    counting at every `n`, not just at primes. -/
def spec_totient_lt (impl : RepoImpl) : Prop :=
  ∀ (n : Nat), 2 ≤ n → impl.ntheory.totient n < n

/-- Totient divisor-sum identity: for every `n ≥ 1`, summing `totient` over
    all positive divisors of `n` returns exactly `n` — `∑_{d ∣ n} totient(d)
    = n`. Stated against the frozen `divisorsOf` enumeration and the frozen
    `+`-fold. For example at `n = 6` the divisors are `1, 2, 3, 6` and the
    identity forces `φ1 + φ2 + φ3 + φ6 = 1 + 1 + 2 + 2 = 6`. -/
def spec_totient_divisor_sum (impl : RepoImpl) : Prop :=
  ∀ (n : Nat), 1 ≤ n →
    ((divisorsOf n).map impl.ntheory.totient).foldl (· + ·) 0 = n

-- ════════════════════════════════════════════════════════════════
-- Multiplicative-order / discrete-log / square-root laws, stated against
-- Lean's `^`, `%`, `*`, `∣`, `≤`, `<` over an unbounded numeric domain.
-- ════════════════════════════════════════════════════════════════

/-- Multiplicative-order exponent law: when `a` has a (found) multiplicative
    order mod `n`, an exponent `k` returns `a` to `1` mod `n` *exactly* when
    the order divides `k` — `a^k ≡ 1 (mod n) ↔ nOrder a n ∣ k`. Both
    directions are universal over the unbounded exponent `k`; anchored on
    frozen `^`/`%`/`∣`. The order is reached via `impl.ntheory.nOrder`. -/
def spec_n_order_pow_eq_one_iff (impl : RepoImpl) : Prop :=
  ∀ (a n k : Nat),
    0 < impl.ntheory.nOrder a n →
      ((a ^ k) % n = 1 % n ↔ (impl.ntheory.nOrder a n) ∣ k)

/-- Multiplicative order `1` characterization: `a` has order `1` mod `n`
    (in the found-order case) exactly when `a ≡ 1 (mod n)`. Ties the order
    value `1` to the frozen congruence `a % n = 1 % n`. -/
def spec_n_order_one_iff (impl : RepoImpl) : Prop :=
  ∀ (a n : Nat),
    0 < impl.ntheory.nOrder a n →
      (impl.ntheory.nOrder a n = 1 ↔ a % n = 1 % n)

/-- Discrete-log order shift: if `b^x ≡ a (mod n)` is the reported discrete
    log and `b` has a (found) order mod `n`, then shifting the exponent by
    that order is again a solution — `b^(x + nOrder b n) ≡ a (mod n)`.
    Anchored on frozen `^`/`%`; reaches both `discreteLog` and `nOrder`. -/
def spec_discrete_log_order_periodic (impl : RepoImpl) : Prop :=
  ∀ (n a b x : Nat),
    impl.ntheory.discreteLog n a b = some x →
      0 < impl.ntheory.nOrder b n →
        (b ^ (x + impl.ntheory.nOrder b n)) % n = a % n

/-- Discrete-log order-multiple law (universal strengthening of the shift):
    when `discreteLog n a b = some x` and `b` has a (found) order mod `n`,
    *every* exponent of the form `x + j · nOrder b n` is again a solution —
    `b^(x + j·nOrder b n) ≡ a (mod n)` for all `j`. Universal over `j`. -/
def spec_discrete_log_order_multiple (impl : RepoImpl) : Prop :=
  ∀ (n a b x : Nat),
    impl.ntheory.discreteLog n a b = some x →
      0 < impl.ntheory.nOrder b n →
        ∀ j, (b ^ (x + j * impl.ntheory.nOrder b n)) % n = a % n

/-- Square-root complement law: if `r` is the reported square root of `a`
    mod `p`, then its complement `p - r` is *also* a square root —
    `(p - r)·(p - r) ≡ a (mod p)`. Anchored on frozen `*`/`%`/`-`. -/
def spec_sqrt_mod_complement (impl : RepoImpl) : Prop :=
  ∀ (a p r : Nat),
    impl.ntheory.sqrtMod a p = some r →
      ((p - r) * (p - r)) % p = a % p

/-- Square-root canonical-bound law: the reported (canonical, least) square
    root `r` never exceeds its own complement — `r ≤ p - r`. Pins the
    canonical representative to the lower half of each complementary pair,
    against frozen `≤`/`-`. -/
def spec_sqrt_mod_least_le_complement (impl : RepoImpl) : Prop :=
  ∀ (a p r : Nat),
    impl.ntheory.sqrtMod a p = some r → r ≤ p - r

-- ════════════════════════════════════════════════════════════════
-- Deep counting / positional laws over derived enumerations, stated as
-- clean end-facts. Each pins a totient / discrete-log / square-root value
-- through a global identity over an unbounded family; anchored on frozen
-- `^`/`%`/`*`/`∣`/`+`/`Nat.gcd` and the frozen `List.range` enumeration.
-- ════════════════════════════════════════════════════════════════

/-- Totient square law: `totient (n·n) = n · totient n` for every `n`. A
    single clean multiplicative identity relating the unit count at `n·n`
    to the unit count at `n`, universal over the unbounded `n`; anchored on
    frozen `*` and the totient unit count. No finite table of totient values
    satisfies it across all `n`. -/
def spec_totient_square_lift (impl : RepoImpl) : Prop :=
  ∀ (n : Nat), impl.ntheory.totient (n * n) = n * impl.ntheory.totient n

/-- Totient prime-power law (frozen-divisibility-anchored): for every `p ≥ 2`
    that carries the primality certificate (no divisor `d` with `1 < d < p`)
    and every `k`, the unit count at `p^(k+1)` together with `p^k` recovers
    the modulus — `totient (p^(k+1)) + p^k = p^(k+1)`. Universal over the
    unbounded prime family and exponent `k`; anchored on frozen `^`/`+`/`∣`. -/
def spec_totient_prime_power (impl : RepoImpl) : Prop :=
  ∀ (p k : Nat),
    2 ≤ p → (∀ d, 1 < d → d < p → ¬ (d ∣ p)) →
      impl.ntheory.totient (p ^ (k + 1)) + p ^ k = p ^ (k + 1)

/-- Discrete-log order class count: when `discreteLog n a b = some x` is a
    reported log and `b` has a found order `d = nOrder b n > 0`, then over
    the initial segment `[0, t·d)` of exponents exactly `t` solve
    `b^y ≡ a (mod n)` — `((range (t·d)).filter (b^y ≡ a)).length = t`.
    Universal over the unbounded window multiplier `t`; anchored on frozen
    `^`/`%`/`*` and the frozen `List.range`/`filter` enumeration. -/
def spec_discrete_log_order_class_count (impl : RepoImpl) : Prop :=
  ∀ (n a b x t : Nat),
    impl.ntheory.discreteLog n a b = some x →
      0 < impl.ntheory.nOrder b n →
        ((List.range (t * impl.ntheory.nOrder b n)).filter
          (fun y => (b ^ y) % n == a % n)).length = t

/-- Square-root prefix law: if `r` is the reported square root of `a` mod `p`,
    then over the initial segment `[0, r]` of residues the only one squaring
    to `a` is `r` itself — `((range (r+1)).filter (x·x ≡ a)).length = [r]` as
    a list. A clean positional end-fact over the frozen `List.range`/`filter`
    enumeration, universal over `a`, `p`, `r`; anchored on frozen `*`/`%`. -/
def spec_sqrt_mod_prefix_singleton (impl : RepoImpl) : Prop :=
  ∀ (a p r : Nat),
    impl.ntheory.sqrtMod a p = some r →
      (List.range (r + 1)).filter (fun x => (x * x) % p == a % p) = [r]

-- ════════════════════════════════════════════════════════════════
-- Jacobi character laws over UNBOUNDEDLY MANY odd moduli. Each is a
-- universal law over an infinite family, so no finite lookup table of
-- probed moduli can satisfy it — the value is pinned by the standard
-- Jacobi character structure (numerator/denominator multiplicativity,
-- reciprocity, prime specialization, and the vanishing characterization),
-- all stated against frozen `*`/`%`/`∣`/`Nat.gcd` and the `Int` numerator.
-- ════════════════════════════════════════════════════════════════

/-- Jacobi numerator multiplicativity (complete character in the numerator):
    for every odd denominator `n`, `(a·b / n) = (a / n)·(b / n)` for all
    integer numerators `a`, `b`. A single universal law over the unbounded odd
    denominator family; a shared factor with `n` sends both sides to `0`, and
    otherwise the symbols lie in `{-1, 1}` and compose as a character. No finite
    table of moduli can satisfy the `∀ a b n` quantification. -/
def spec_jacobi_mul_numerator (impl : RepoImpl) : Prop :=
  ∀ (a b : Int) (n : Nat),
    n % 2 = 1 →
      impl.ntheory.jacobiSymbol (a * b) n =
        impl.ntheory.jacobiSymbol a n * impl.ntheory.jacobiSymbol b n

/-- Jacobi denominator multiplicativity: for odd `m`, `n`, the symbol splits
    over the denominator product — `(a / m·n) = (a / m)·(a / n)` for every
    integer numerator `a`, including repeated prime factors and numerators
    sharing a factor with a denominator. Pins the symbol at infinitely many
    composite odd moduli, not just primes; anchored on frozen `*`. -/
def spec_jacobi_mul_denominator (impl : RepoImpl) : Prop :=
  ∀ (a : Int) (m n : Nat),
    m % 2 = 1 → n % 2 = 1 →
      impl.ntheory.jacobiSymbol a (m * n) =
        impl.ntheory.jacobiSymbol a m * impl.ntheory.jacobiSymbol a n

/-- Jacobi specializes to Legendre at every odd prime (Euler-criterion
    agreement over the unbounded prime family): for every `p` carrying the
    frozen primality certificate with `p` odd, and every numerator `a`, the
    Jacobi symbol equals the Legendre symbol. Generalizes any finite prime
    table to all odd primes, forcing agreement with genuine quadratic
    residuosity at unboundedly many moduli. -/
def spec_jacobi_legendre_all_odd_primes (impl : RepoImpl) : Prop :=
  ∀ (a p : Nat),
    isPrimeCert p → p % 2 = 1 →
      impl.ntheory.jacobiSymbol (a : Int) p = impl.ntheory.legendreSymbol a p

/-- Jacobi reciprocity sign law (global, over every coprime odd pair): for
    coprime positive odd `m`, `n`, the product `(m / n)·(n / m)` is `-1`
    exactly when both `m ≡ 3` and `n ≡ 3 (mod 4)`, and `1` otherwise. A single
    universal reciprocity invariant over the infinite coprime-odd family;
    anchored on frozen `%`/`*`/`Nat.gcd`. -/
def spec_jacobi_reciprocity (impl : RepoImpl) : Prop :=
  ∀ (m n : Nat),
    m % 2 = 1 → n % 2 = 1 → Nat.gcd m n = 1 →
      impl.ntheory.jacobiSymbol (m : Int) n * impl.ntheory.jacobiSymbol (n : Int) m =
        (if m % 4 = 3 ∧ n % 4 = 3 then (-1 : Int) else 1)

/-- Jacobi vanishing characterization (over every odd denominator): for odd
    `n`, the symbol is `0` exactly when the reduced numerator shares a factor
    with `n` — `(a / n) = 0 ↔ gcd(intResidue a n, n) ≠ 1`. Couples the frozen
    signed reduction to `Nat.gcd` over the unbounded odd family; the bad cases
    are determined by arbitrary common factors, not fixed sampled moduli. -/
def spec_jacobi_zero_iff_not_coprime (impl : RepoImpl) : Prop :=
  ∀ (a : Int) (n : Nat),
    n % 2 = 1 →
      (impl.ntheory.jacobiSymbol a n = 0 ↔ Nat.gcd (intResidue a n) n ≠ 1)

-- ════════════════════════════════════════════════════════════════
-- Totient identities over derived gcd-enumerations, and multiplicative-order
-- divisibility. Each pins a value as a clean end-fact; anchored on frozen
-- `Nat.gcd`/`%`/`∣`/`*`/`+`, `List.range`/`filter`, and the frozen
-- `divisorsOf` enumeration.
-- ════════════════════════════════════════════════════════════════

/-- Totient multiplicativity on coprime moduli: `totient (m·n) = totient m ·
    totient n` whenever `gcd m n = 1`. A clean end-fact over the unbounded
    coprime pair, anchored on frozen `*`/`Nat.gcd`. -/
def spec_totient_mul_coprime (impl : RepoImpl) : Prop :=
  ∀ (m n : Nat),
    Nat.gcd m n = 1 →
      impl.ntheory.totient (m * n) = impl.ntheory.totient m * impl.ntheory.totient n

/-- Totient gcd-fiber count: for every positive divisor `d` of `n`, the number
    of `k` in `[1, n]` with `gcd(k, n) = d` is exactly `totient (n / d)`. A
    derived-enumeration partition identity — filtered positions `i + 1` grouped
    by their gcd — pinned against the frozen `totient` count; universal over
    `n` and its divisors, anchored on frozen `Nat.gcd`/`∣`/`/`. -/
def spec_totient_gcd_fiber_count (impl : RepoImpl) : Prop :=
  ∀ (n d : Nat),
    1 ≤ n → 0 < d → d ∣ n →
      ((List.range n).filter (fun i => Nat.gcd (i + 1) n == d)).length =
        impl.ntheory.totient (n / d)

/-- Totient gcd-sum identity: `∑_{k=1}^{n} gcd(k, n) = ∑_{d ∣ n} d · totient(n/d)`.
    The complete divisor-weighted gcd sum, stated against the frozen
    `List.range` gcd-enumeration on the left and the frozen `divisorsOf`
    enumeration on the right. Anchored on frozen `Nat.gcd`/`*`/`+`. -/
def spec_totient_gcd_sum (impl : RepoImpl) : Prop :=
  ∀ (n : Nat),
    1 ≤ n →
      ((List.range n).map (fun i => Nat.gcd (i + 1) n)).foldl (· + ·) 0 =
        ((divisorsOf n).map (fun d => d * impl.ntheory.totient (n / d))).foldl (· + ·) 0

/-- Multiplicative-order divisibility: every unit `a` modulo `n ≥ 2`
    (`gcd a n = 1`) has a found positive order that divides the unit count —
    `0 < nOrder a n ∧ nOrder a n ∣ totient n`. A clean end-fact tying the
    `nOrder` search result to the `totient` count, anchored on frozen
    `Nat.gcd`/`∣`. -/
def spec_n_order_divides_totient (impl : RepoImpl) : Prop :=
  ∀ (a n : Nat),
    2 ≤ n → Nat.gcd a n = 1 →
      0 < impl.ntheory.nOrder a n ∧
        impl.ntheory.nOrder a n ∣ impl.ntheory.totient n

-- ════════════════════════════════════════════════════════════════
-- Discrete-log / root cardinality laws over derived enumerations. Each is a
-- counting / canonical-uniqueness end-fact over a cyclic power orbit or a
-- field root set; anchored on frozen `^`/`%`/`*`/`Nat.gcd` and the frozen
-- `List.range`/`filter` enumeration.
-- ════════════════════════════════════════════════════════════════

/-- Discrete-log image count equals the order: when the base `b` has a found
    order `d = nOrder b n > 0`, exactly `d` of the residues `a < n` admit a
    discrete log to base `b` — `((range n).filter (discreteLog n a b).isSome).length
    = nOrder b n`. A counting-over-derived-enumeration law: the powers of `b`
    cycle with period `d`, so the reachable residues number exactly `d`.
    Anchored on frozen `^`/`%` and the frozen `List.range`/`filter`. -/
def spec_discrete_log_image_count (impl : RepoImpl) : Prop :=
  ∀ (n b : Nat),
    0 < impl.ntheory.nOrder b n →
      ((List.range n).filter
        (fun a => (impl.ntheory.discreteLog n a b).isSome)).length =
        impl.ntheory.nOrder b n

/-- Discrete-log shifted order-class count: when `discreteLog n a b = some x`
    and `b` has a found order `d`, then over *any* shifted window
    `[offset, offset + t·d)` of exponents exactly `t` solve `b^y ≡ a (mod n)`.
    A clean count end-fact, universal over `offset` and `t`; anchored on frozen
    `^`/`%` and the frozen `List.range`/`filter`. -/
def spec_discrete_log_shifted_order_class_count (impl : RepoImpl) : Prop :=
  ∀ (n a b x offset t : Nat),
    impl.ntheory.discreteLog n a b = some x →
      0 < impl.ntheory.nOrder b n →
        ((List.range (t * impl.ntheory.nOrder b n)).filter
          (fun j => (b ^ (offset + j)) % n == a % n)).length = t

/-- Square-root pair over an odd prime (exactly two roots, canonical lower):
    for an odd prime `p` (frozen certificate) and nonzero `a`, if `sqrtMod`
    returns `r` then the complete root list over `[0, p)` is exactly `[r, p-r]`
    — the two distinct roots of a nonzero square in a field, with the canonical
    `find?` root first. A positional + at-most-two-roots end-fact over the full
    residue enumeration; anchored on frozen `*`/`%`/`-`. -/
def spec_sqrt_mod_odd_prime_roots_pair (impl : RepoImpl) : Prop :=
  ∀ (a p r : Nat),
    2 < p → p % 2 = 1 → isPrimeCert p → a % p ≠ 0 →
      impl.ntheory.sqrtMod a p = some r →
        (List.range p).filter (fun x => (x * x) % p == a % p) = [r, p - r]

/-- `nthrootMod` unique root when the exponent is coprime to `p-1` (permutation
    of an odd prime field): for an odd prime `p` (frozen certificate) and `k`
    with `gcd(k, p-1) = 1`, exponentiation by `k` permutes the residues, so
    every `a` has a *unique* `k`-th root — `nthrootMod a k p` succeeds and the
    complete root list over `[0, p)` is the singleton `[r]`. A finite-field
    automorphism + canonical-uniqueness end-fact; anchored on frozen `^`/`%`. -/
def spec_nthroot_prime_coprime_unique (impl : RepoImpl) : Prop :=
  ∀ (a k p : Nat),
    2 < p → p % 2 = 1 → isPrimeCert p → Nat.gcd k (p - 1) = 1 →
      ∃ r, impl.ntheory.nthrootMod a k p = some r ∧
        (List.range p).filter (fun x => (x ^ k) % p == a % p) = [r]

-- ════════════════════════════════════════════════════════════════
-- Euler / universal-exponent, primitive-root count, order-of-a-power,
-- Legendre & Jacobi supplement laws, Euler's criterion, and discrete-log
-- homomorphism laws. Each states a clean end-fact over an unbounded family;
-- anchored on frozen `^`/`%`/`*`/`∣`/`≤`/`<`/`Nat.gcd` and the frozen
-- `totient`/`nOrder`/`discreteLog`/`legendreSymbol`/`jacobiSymbol` values.
-- ════════════════════════════════════════════════════════════════

/-- Euler's theorem (universal exponent): every unit `a` mod `n ≥ 1`
    (`gcd a n = 1`) is returned to `1` by the totient exponent —
    `a^(totient n) ≡ 1 (mod n)`. A clean end-fact over the unbounded unit
    family tying the frozen `totient` count to the frozen congruence
    `^`/`%`; universal over both `a` and `n`. -/
def spec_euler_theorem_units (impl : RepoImpl) : Prop :=
  ∀ (a n : Nat),
    1 ≤ n → Nat.gcd a n = 1 →
      (a ^ impl.ntheory.totient n) % n = 1 % n

/-- Quadratic-residue count at an odd prime: exactly `(p-1)/2` of the nonzero
    residues `a < p` are quadratic residues — half of the multiplicative
    residues are squares. A counting end-fact over the frozen `List.range`
    enumeration and the frozen residue predicate; universal over the odd-prime
    family (frozen certificate). -/
def spec_quadratic_residue_count_odd_prime (impl : RepoImpl) : Prop :=
  ∀ (p : Nat),
    2 < p → p % 2 = 1 → isPrimeCert p →
      ((List.range p).filter
        (fun a => a != 0 && impl.ntheory.isQuadraticResidue a p)).length =
        (p - 1) / 2

/-- Primitive-root count at a prime: the number of residues `a < p` whose
    multiplicative order equals `p-1` is exactly `totient (p-1)`. A counting
    end-fact over the frozen `List.range`/`filter` enumeration, pinned against
    the frozen `nOrder` and `totient` values; universal over the prime family
    (frozen certificate). -/
def spec_primitive_root_count_prime (impl : RepoImpl) : Prop :=
  ∀ (p : Nat),
    isPrimeCert p →
      ((List.range p).filter
        (fun a => impl.ntheory.nOrder a p == p - 1)).length =
        impl.ntheory.totient (p - 1)

/-- Legendre first supplement: `(-1 / p)` is `1` exactly when `p ≡ 1 (mod 4)`
    and `-1` when `p ≡ 3 (mod 4)`, stated at the residue `p-1 ≡ -1`. Pins the
    symbol at `-1` over the unbounded odd-prime family against frozen `%`. -/
def spec_legendre_neg_one_supplement (impl : RepoImpl) : Prop :=
  ∀ (p : Nat),
    isPrimeCert p → p % 2 = 1 →
      impl.ntheory.legendreSymbol (p - 1) p =
        (if p % 4 = 1 then (1 : Int) else (-1 : Int))

/-- Legendre second supplement: `(2 / p)` is `1` for `p ≡ 1, 7 (mod 8)` and
    `-1` for `p ≡ 3, 5 (mod 8)`. Pins the symbol at the numerator `2` over the
    unbounded odd-prime family against frozen `%`. -/
def spec_legendre_two_supplement (impl : RepoImpl) : Prop :=
  ∀ (p : Nat),
    isPrimeCert p → p % 2 = 1 →
      impl.ntheory.legendreSymbol 2 p =
        (if p % 8 = 1 ∨ p % 8 = 7 then (1 : Int) else (-1 : Int))

/-- Jacobi second supplement: for odd `n ≥ 1`, `(2 / n)` is `1` when
    `n ≡ 1, 7 (mod 8)` and `-1` when `n ≡ 3, 5 (mod 8)`. Extends the Legendre
    `2`-supplement to every odd denominator; universal over the odd family,
    anchored on frozen `%`. -/
def spec_jacobi_two_supplement (impl : RepoImpl) : Prop :=
  ∀ (n : Nat),
    0 < n → n % 2 = 1 →
      impl.ntheory.jacobiSymbol 2 n =
        (if n % 8 = 1 ∨ n % 8 = 7 then (1 : Int) else (-1 : Int))

/-- Euler's criterion: for an odd prime `p`, the Legendre symbol reduced into
    `[0, p)` equals `a^((p-1)/2)` mod `p` — `((legendreSymbol a p + p) % p).toNat
    = a^((p-1)/2) % p`, with `-1` represented as `p-1`. Couples the frozen
    symbol to a frozen power congruence over the unbounded odd-prime family and
    every numerator `a`; anchored on frozen `^`/`%`/`+`. -/
def spec_legendre_euler_criterion (impl : RepoImpl) : Prop :=
  ∀ (a p : Nat),
    isPrimeCert p → p % 2 = 1 →
      (((impl.ntheory.legendreSymbol a p + (p : Int)) % (p : Int)).toNat =
        (a ^ ((p - 1) / 2)) % p)

/-- Order of a power: for a unit `a` mod `n ≥ 2` (`gcd a n = 1`) and every
    exponent `k`, the order of `a^k` is `nOrder a n / gcd(nOrder a n, k)`. A
    single clean identity relating the order of a power to the base order over
    the unbounded `(a, k, n)` family; anchored on frozen `^`/`Nat.gcd`/`/`. -/
def spec_n_order_power_quotient (impl : RepoImpl) : Prop :=
  ∀ (a k n : Nat),
    2 ≤ n → Nat.gcd a n = 1 →
      impl.ntheory.nOrder (a ^ k) n =
        impl.ntheory.nOrder a n / Nat.gcd (impl.ntheory.nOrder a n) k

/-- Discrete-log image over one period: when `b` has a found order `d =
    nOrder b n > 0`, a residue `a` admits a discrete log to base `b` exactly
    when some exponent `x < d` already realizes it — `(discreteLog n a b).isSome
    ↔ ∃ x < d, b^x ≡ a (mod n)`. Pins the solvable set to one period of the
    base's power cycle; anchored on frozen `^`/`%`, universal over `a`. -/
def spec_discrete_log_image_one_period (impl : RepoImpl) : Prop :=
  ∀ (n a b : Nat),
    0 < impl.ntheory.nOrder b n →
      ((impl.ntheory.discreteLog n a b).isSome = true ↔
        ∃ x, x < impl.ntheory.nOrder b n ∧ (b ^ x) % n = a % n)

/-- Discrete-log homomorphism: when `discreteLog n a b = some x` and
    `discreteLog n c b = some y` and `b` has a found order `d`, the product
    `a·c` is again solvable and its log adds mod `d` — `∃ z, discreteLog n (a·c)
    b = some z ∧ z ≡ x + y (mod d)`. Ties multiplication of targets to addition
    of logs over the unbounded family; anchored on frozen `*`/`^`/`%`. -/
def spec_discrete_log_mul_homomorphism (impl : RepoImpl) : Prop :=
  ∀ (n a c b x y : Nat),
    impl.ntheory.discreteLog n a b = some x →
      impl.ntheory.discreteLog n c b = some y →
        0 < impl.ntheory.nOrder b n →
          ∃ z,
            impl.ntheory.discreteLog n (a * c) b = some z ∧
              z % impl.ntheory.nOrder b n =
                (x + y) % impl.ntheory.nOrder b n
