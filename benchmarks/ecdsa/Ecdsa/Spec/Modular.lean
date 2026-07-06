import Ecdsa.Harness

/-!
# Ecdsa.Spec.Modular

Specifications for the GF(p) modular-arithmetic primitives. Each `spec_*` is a
property over an arbitrary `impl : RepoImpl`; an API is reached through
`impl.ecdsa.<fn>`.

The headline obligation `spec_inverse_mod_correct` characterizes the modular
inverse by witness ∧ uniqueness: the equation `(a · inv) % m = 1` and the range
clause `0 < inv ∧ inv < m`, over all coprime `(a, m)`. `spec_inverse_mod_unique`
states the uniqueness directly. The square-root specs are anchored against
concrete primality / Legendre-symbol vectors (`spec_is_odd_prime_concrete`,
`spec_jacobi_concrete`) so `spec_sqrt_mod_prime_squares_back` is grounded.

DO NOT MODIFY.
-/

-- ════════════════════════════════════════════════════════════════
-- inverseMod: witness ∧ uniqueness of the modular inverse
-- ════════════════════════════════════════════════════════════════

/-- Modular-inverse correctness: for `m > 1` and `a` coprime to `m`,
    `inverseMod a m` is the unique residue `inv ∈ [1, m)` with `(a · inv) % m = 1`.
    Witness — the equation `(a · inv) % m = 1`; uniqueness — the range
    `0 < inv ∧ inv < m`. -/
def spec_inverse_mod_correct (impl : RepoImpl) : Prop :=
  ∀ (a m : Nat), 1 < m → Nat.gcd a m = 1 →
    0 < impl.ecdsa.inverseMod a m ∧
    impl.ecdsa.inverseMod a m < m ∧
    (a * impl.ecdsa.inverseMod a m) % m = 1

/-- Range law: for `m > 1` the inverse is always a residue below `m`, for any
    `a` (no coprimality needed). -/
def spec_inverse_mod_range (impl : RepoImpl) : Prop :=
  ∀ (a m : Nat), 1 < m → impl.ecdsa.inverseMod a m < m

/-- Uniqueness of the modular inverse: any residue `b ∈ [0, m)` that satisfies
    `(a · b) % m = 1` equals `inverseMod a m` — the inverse is single-valued, so
    the impl must return the canonical residue. -/
def spec_inverse_mod_unique (impl : RepoImpl) : Prop :=
  ∀ (a m b : Nat), 1 < m → Nat.gcd a m = 1 → b < m → (a * b) % m = 1 →
    b = impl.ecdsa.inverseMod a m

/-- Inverse of `1` is `1` (concrete frozen anchor): `inverseMod 1 m = 1` for
    `m > 1`. Grounds the inverse at the identity residue; an impl off by a
    constant fails here. -/
def spec_inverse_mod_one (impl : RepoImpl) : Prop :=
  ∀ (m : Nat), 1 < m → impl.ecdsa.inverseMod 1 m = 1

/-- Double-inverse law: for any residue coprime to `m > 1`, inverting the
    returned inverse gives back the original residue reduced modulo `m` —
    `inverseMod (inverseMod a m) m = a % m`. -/
def spec_inverse_mod_involutive (impl : RepoImpl) : Prop :=
  ∀ (a m : Nat), 1 < m → Nat.gcd a m = 1 →
    impl.ecdsa.inverseMod (impl.ecdsa.inverseMod a m) m = a % m

/-- Product law: the inverse of a product of two coprime residues is the product
    of their inverses, reduced modulo the same modulus —
    `inverseMod ((a * b) % m) m = (inverseMod a m * inverseMod b m) % m`. -/
def spec_inverse_mod_mul_hom (impl : RepoImpl) : Prop :=
  ∀ (a b m : Nat), 1 < m → Nat.gcd a m = 1 → Nat.gcd b m = 1 →
    impl.ecdsa.inverseMod ((a * b) % m) m =
      (impl.ecdsa.inverseMod a m * impl.ecdsa.inverseMod b m) % m

-- ════════════════════════════════════════════════════════════════
-- isOddPrime / jacobi: frozen guards (anchor the square-root branch)
-- ════════════════════════════════════════════════════════════════

/-- Primality-guard concrete anchor: `isOddPrime` returns the right Bool at a
    table of fixed inputs. This pins the guard so `spec_sqrt_mod_prime_squares_back`
    cannot be satisfied vacuously by a degenerate `isOddPrime := fun _ => false`. -/
def spec_is_odd_prime_concrete (impl : RepoImpl) : Prop :=
  impl.ecdsa.isOddPrime 7 = true ∧
  impl.ecdsa.isOddPrime 13 = true ∧
  impl.ecdsa.isOddPrime 17 = true ∧
  impl.ecdsa.isOddPrime 9 = false ∧
  impl.ecdsa.isOddPrime 2 = false ∧
  impl.ecdsa.isOddPrime 1 = false

/-- Primality characterization (frozen-op-anchored): `isOddPrime p = true`
    exactly when `p > 2`, `p` is odd, and `p` has no divisor `d` with `2 ≤ d < p`.
    Pins the guard to the genuine number-theoretic primality relation over the
    UNBOUNDED domain of all `p`, not just the concrete table — so a lookup-table
    `isOddPrime` that lies elsewhere is rejected. -/
def spec_is_odd_prime_iff (impl : RepoImpl) : Prop :=
  ∀ (p : Nat),
    impl.ecdsa.isOddPrime p = true ↔
      (2 < p ∧ p % 2 = 1 ∧ ∀ d, 2 ≤ d → d < p → p % d ≠ 0)

/-- Legendre-symbol concrete anchor: `jacobi` at fixed inputs. `2` is a
    quadratic residue mod `7` (`3² = 9 ≡ 2`), `3` is a non-residue mod `7`, and
    `2` is a residue mod `17` (`6² = 36 ≡ 2`). Pins the Legendre-symbol guard so
    `spec_sqrt_mod_prime_squares_back` is anchored at genuine residues. -/
def spec_jacobi_concrete (impl : RepoImpl) : Prop :=
  impl.ecdsa.jacobi 2 7 = 1 ∧
  impl.ecdsa.jacobi 3 7 = -1 ∧
  impl.ecdsa.jacobi 2 17 = 1 ∧
  impl.ecdsa.jacobi 0 7 = 0

-- ════════════════════════════════════════════════════════════════
-- sqrtModPrime: squares-back, anchored (never agent-vacuous)
-- ════════════════════════════════════════════════════════════════

/-- Square-root squares-back at frozen residue vectors: where a quadratic
    residue genuinely exists (anchored by the concrete `jacobi`/`isOddPrime`
    vectors above), `sqrtModPrime a p` returns a residue squaring back to `a`.
    Stated at fixed `(a, p)` pairs that are real residues — `2 mod 7`, `4 mod 7`,
    `2 mod 17`, `9 mod 17` — so the obligation is grounded and cannot be dodged
    by returning a junk constant. -/
def spec_sqrt_mod_prime_squares_back (impl : RepoImpl) : Prop :=
  (let r := impl.ecdsa.sqrtModPrime 2 7;  (r * r) % 7 = 2 % 7) ∧
  (let r := impl.ecdsa.sqrtModPrime 4 7;  (r * r) % 7 = 4 % 7) ∧
  (let r := impl.ecdsa.sqrtModPrime 2 17; (r * r) % 17 = 2 % 17) ∧
  (let r := impl.ecdsa.sqrtModPrime 9 17; (r * r) % 17 = 9 % 17)

/-- Square-root range at the frozen vectors: the returned root is a residue
    below the modulus. Companion to `spec_sqrt_mod_prime_squares_back`, pinning
    the output domain. -/
def spec_sqrt_mod_prime_range (impl : RepoImpl) : Prop :=
  impl.ecdsa.sqrtModPrime 2 7 < 7 ∧
  impl.ecdsa.sqrtModPrime 2 17 < 17 ∧
  impl.ecdsa.sqrtModPrime 9 17 < 17

/-- General square-root law: for any odd-prime modulus where a square root of
    the input residue exists, `sqrtModPrime` returns a value whose square is the
    input residue. Grounded over the unbounded `(a, p)` domain, not a fixed
    table. -/
def spec_sqrt_mod_prime_squares_back_general (impl : RepoImpl) : Prop :=
  ∀ (a p : Nat), impl.ecdsa.isOddPrime p = true →
    (∃ r, r < p ∧ (r * r) % p = a % p) →
      let s := impl.ecdsa.sqrtModPrime a p
      (s * s) % p = a % p

/-- Greatest-root law: any residue at most `p` whose square is the input
    residue is no larger than the value returned by `sqrtModPrime a p`. -/
def spec_sqrt_mod_prime_greatest_root (impl : RepoImpl) : Prop :=
  ∀ (a p r : Nat), r ≤ p → (r * r) % p = a % p →
    r ≤ impl.ecdsa.sqrtModPrime a p

/-- Nonzero-residue range law: for a positive modulus and nonzero input
    residue, `sqrtModPrime a p` returns a value below the modulus. -/
def spec_sqrt_mod_prime_nonzero_range (impl : RepoImpl) : Prop :=
  ∀ (a p : Nat), 0 < p → a % p ≠ 0 →
    impl.ecdsa.sqrtModPrime a p < p

/-- Degenerate-modulus boundary law for the Jacobi symbol (GENERAL, over all
    numerators `a`): the symbol is undefined for a unit modulus, so the guard
    reports `0`. `jacobi a 1 = 0` for every `a`. This is the `n ≤ 1` boundary of
    the Legendre/Jacobi recurrence; it holds for the whole unbounded numerator
    domain, not just a sampled point, so a `jacobi` that mishandled the trivial
    modulus is rejected everywhere. -/
def spec_jacobi_denom_one (impl : RepoImpl) : Prop :=
  ∀ (a : Nat), impl.ecdsa.jacobi a 1 = 0

-- ════════════════════════════════════════════════════════════════
-- jacobi at an odd-prime modulus: multiplicativity + classification
-- ════════════════════════════════════════════════════════════════

/-- Multiplicativity at an odd-prime modulus: the Legendre symbol of a product
    residue is the product of the two symbols —
    `jacobi ((a * b) % p) p = jacobi a p * jacobi b p` for every `p` with
    `isOddPrime p = true`. Over `impl.ecdsa.isOddPrime`, `impl.ecdsa.jacobi`,
    `*`, `%`. -/
def spec_jacobi_prime_mul (impl : RepoImpl) : Prop :=
  ∀ (a b p : Nat), impl.ecdsa.isOddPrime p = true →
    impl.ecdsa.jacobi ((a * b) % p) p =
      impl.ecdsa.jacobi a p * impl.ecdsa.jacobi b p

/-- Zero classification at an odd-prime modulus: `jacobi a p = 0` exactly when
    `p` divides the numerator, i.e. `a % p = 0`, for every `p` with
    `isOddPrime p = true`. Over `impl.ecdsa.isOddPrime`, `impl.ecdsa.jacobi`,
    `%`. -/
def spec_jacobi_prime_zero_iff (impl : RepoImpl) : Prop :=
  ∀ (a p : Nat), impl.ecdsa.isOddPrime p = true →
    (impl.ecdsa.jacobi a p = 0 ↔ a % p = 0)

/-- Residue classification at an odd-prime modulus: every nonzero square residue
    has Legendre symbol `1` — `a % p ≠ 0 → jacobi ((a * a) % p) p = 1` for every
    `p` with `isOddPrime p = true`. Over `impl.ecdsa.isOddPrime`,
    `impl.ecdsa.jacobi`, `*`, `%`. -/
def spec_jacobi_prime_square_nonzero (impl : RepoImpl) : Prop :=
  ∀ (a p : Nat), impl.ecdsa.isOddPrime p = true → a % p ≠ 0 →
    impl.ecdsa.jacobi ((a * a) % p) p = 1

-- ════════════════════════════════════════════════════════════════
-- inverseMod: residue-only dependence + self-inverse characterization
-- ════════════════════════════════════════════════════════════════

/-- Residue-only dependence: reducing the numerator modulo `m` before inverting
    leaves the result unchanged — `inverseMod (a % m) m = inverseMod a m` for
    `m > 1`. Over `impl.ecdsa.inverseMod`, `%`. -/
def spec_inverse_mod_residue_arg (impl : RepoImpl) : Prop :=
  ∀ (a m : Nat), 1 < m →
    impl.ecdsa.inverseMod (a % m) m = impl.ecdsa.inverseMod a m

/-- Self-inverse characterization: a residue coprime to `m > 1` equals its own
    inverse exactly when its square is `1` modulo `m` —
    `inverseMod a m = a % m ↔ (a * a) % m = 1`. Over `impl.ecdsa.inverseMod`,
    `Nat.gcd`, `*`, `%`. -/
def spec_inverse_mod_self_iff_square_one (impl : RepoImpl) : Prop :=
  ∀ (a m : Nat), 1 < m → Nat.gcd a m = 1 →
    (impl.ecdsa.inverseMod a m = a % m ↔ (a * a) % m = 1)

-- ════════════════════════════════════════════════════════════════
-- sqrtModPrime: greatest-in-scan selection + failure sentinel
-- ════════════════════════════════════════════════════════════════

/-- Greatest-root selection: whenever some `r ≤ p` squares to the target residue,
    `sqrtModPrime a p` is itself such a root, lies within `[0, p]`, and is at
    least as large as `r` — `(s * s) % p = a % p ∧ r ≤ s ∧ s ≤ p` for
    `s = sqrtModPrime a p`. Over `impl.ecdsa.sqrtModPrime`, `≤`, `*`, `%`. -/
def spec_sqrt_mod_prime_scanned_root_greatest (impl : RepoImpl) : Prop :=
  ∀ (a p r : Nat), r ≤ p → (r * r) % p = a % p →
    let s := impl.ecdsa.sqrtModPrime a p
    (s * s) % p = a % p ∧ r ≤ s ∧ s ≤ p

/-- Failure sentinel: for a positive modulus, `sqrtModPrime a p = 0` exactly when
    no `r ≤ p` squares to the target residue —
    `sqrtModPrime a p = 0 ↔ ∀ r ≤ p, (r * r) % p ≠ a % p`. Over
    `impl.ecdsa.sqrtModPrime`, `≤`, `*`, `%`. -/
def spec_sqrt_mod_prime_zero_iff_no_scanned_root (impl : RepoImpl) : Prop :=
  ∀ (a p : Nat), 0 < p →
    (impl.ecdsa.sqrtModPrime a p = 0 ↔
      ∀ (r : Nat), r ≤ p → (r * r) % p ≠ a % p)

-- ════════════════════════════════════════════════════════════════
-- jacobi equidistribution: the QR / non-residue split at an odd prime
-- ════════════════════════════════════════════════════════════════

/-- Legendre equidistribution at an odd prime: over the residues `[0, p)` the two
    nonzero symbol classes split exactly evenly — there are `(p - 1) / 2` residues
    with `jacobi a p = 1` (the quadratic residues) and `(p - 1) / 2` with
    `jacobi a p = -1` (the non-residues). This is the global counting law behind
    the Legendre symbol, and no degenerate `jacobi` survives it: an all-ones stub
    scores a `-1` count of `0 ≠ (p - 1) / 2`, and any lookup table that is only
    correct on a handful of sampled inputs miscounts on the residues it never saw.
    Unlike the concrete anchors above it constrains the symbol over the whole
    residue range at every odd prime, not at a fixed table of points. Over
    `impl.ecdsa.isOddPrime`, `impl.ecdsa.jacobi`, `List.range`, `List.countP`. -/
def spec_jacobi_equidistribution (impl : RepoImpl) : Prop :=
  ∀ (p : Nat), impl.ecdsa.isOddPrime p = true →
    ((List.range p).countP (fun a => impl.ecdsa.jacobi a p == 1) = (p - 1) / 2)
    ∧ ((List.range p).countP (fun a => impl.ecdsa.jacobi a p == -1) = (p - 1) / 2)
