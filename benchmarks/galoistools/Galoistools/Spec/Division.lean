import Galoistools.Spec.Ring

/-!
# Galoistools.Spec.Division

Specifications for Euclidean division (`gfDiv`), its projections (`gfRem`,
`gfQuo`), the monic gcd (`gfGcd`), and modular exponentiation (`gfPowMod`).

Polynomials are big-endian coeff lists over `GF(p)`; the reference vocabulary is
the frozen **Spec-local** helpers `refGfStrip`, `refGfDegree`, `refLeadCoeff`,
`refGfTrunc` (and the derived `IsNorm` / `PrimeField`) defined in `Spec/Ring.lean`,
plus the scored ring ops. These `ref*` helpers are frozen copies — deliberately
independent of the agent-editable `Impl` helpers of the same base name — so no
spec can be gamed by redefining an implementation helper (see the note in
`Spec/Ring.lean`).

The headline obligation is `spec_div_identity`: for a normalized divisor `g`
with unit leading coefficient, `gfDiv f g p = (q, r)` recomposes to `f`, i.e.
`gfAdd (gfMul q g p) r p = f`, with `r` reduced below `g` in degree
(`spec_div_deg_bound`). The gcd is pinned to divide both inputs
(`spec_gcd_divides_both`) and to be monic (`spec_gcd_monic`), and the modular
exponentiation is pinned by its repeated-squaring recurrence
(`spec_powmod_recurrence`) plus reducedness (`spec_powmod_reduced`).

DO NOT MODIFY.
-/

open Galoistools

-- ════════════════════════════════════════════════════════════════
-- gfRem / gfQuo: projections of gfDiv
-- ════════════════════════════════════════════════════════════════

/-- `gfRem` is the second component of `gfDiv`: `gfRem f g p = (gfDiv f g p).2`.
    Over `impl.galoistools.gfRem`, `impl.galoistools.gfDiv`. -/
def spec_rem_is_div_snd (impl : RepoImpl) : Prop :=
  ∀ (f g : List Nat) (p : Nat), impl.galoistools.gfRem f g p = (impl.galoistools.gfDiv f g p).2

/-- `gfQuo` is the first component of `gfDiv`: `gfQuo f g p = (gfDiv f g p).1`.
    Over `impl.galoistools.gfQuo`, `impl.galoistools.gfDiv`. -/
def spec_quo_is_div_fst (impl : RepoImpl) : Prop :=
  ∀ (f g : List Nat) (p : Nat), impl.galoistools.gfQuo f g p = (impl.galoistools.gfDiv f g p).1

-- ════════════════════════════════════════════════════════════════
-- gfDiv: division identity + degree bound (the headline)
-- ════════════════════════════════════════════════════════════════

/-- Division identity: for `p > 1` and a normalized divisor `g` with unit leading
    coefficient (`refLeadCoeff g = 1`), the quotient/remainder pair `(q, r) =`
    `gfDiv f g p` recomposes to `f` — `gfAdd (gfMul q g p) r p = f` — whenever `f`
    is normalized. This is `f = q·g + r`, the defining property of Euclidean
    division, pinned as a raw coefficient-list equality over the scored ring ops
    `gfAdd`, `gfMul`. A monic divisor makes the quotient unique, so `(q, r)` is the
    unique such pair. Over `impl.galoistools.gfDiv`, `impl.galoistools.gfAdd`,
    `impl.galoistools.gfMul`, `refLeadCoeff`. -/
def spec_div_identity (impl : RepoImpl) : Prop :=
  ∀ (f g : List Nat) (p : Nat), 1 < p → IsNorm p f → IsNorm p g → refLeadCoeff g = 1 →
    let qr := impl.galoistools.gfDiv f g p
    impl.galoistools.gfAdd (impl.galoistools.gfMul qr.1 g p) qr.2 p = f

/-- Uniqueness of the quotient/remainder pair: for a normalized monic divisor `g`,
    any normalized pair `(q', r')` that also recomposes `f`
    (`gfAdd (gfMul q' g) r' = f`) with a below-`g`-degree remainder
    (`r' = [] ∨ refGfDegree r' < refGfDegree g`) equals `gfDiv f g p`. Together
    with `spec_div_identity` and `spec_div_deg_bound` this characterizes Euclidean
    division completely — blocking a "right remainder, wrong quotient"
    implementation. Over `impl.galoistools.gfDiv`, `impl.galoistools.gfAdd`,
    `impl.galoistools.gfMul`, `refGfDegree`, `refLeadCoeff`. -/
def spec_div_unique (impl : RepoImpl) : Prop :=
  ∀ (f g q' r' : List Nat) (p : Nat), 1 < p → IsNorm p f → IsNorm p g →
    refLeadCoeff g = 1 → IsNorm p q' → IsNorm p r' →
    impl.galoistools.gfAdd (impl.galoistools.gfMul q' g p) r' p = f →
    (r' = [] ∨ refGfDegree r' < refGfDegree g) →
    (q', r') = impl.galoistools.gfDiv f g p

/-- Remainder degree bound: over a prime field, for a nonempty divisor `g` whose
    leading coefficient is a unit, the remainder `r = (gfDiv f g p).2` is either
    the zero polynomial or has degree strictly below `g` —
    `r = [] ∨ refGfDegree r < refGfDegree g`. This pins the remainder as genuinely
    reduced. (Primality is required: over a composite modulus a non-invertible
    leading coefficient stalls the reduction and leaves a full-degree remainder.)
    Over `impl.galoistools.gfDiv`, `refGfDegree`. -/
def spec_div_deg_bound (impl : RepoImpl) : Prop :=
  ∀ (f g : List Nat) (p : Nat), PrimeField p → IsNorm p g → g ≠ [] →
    let r := (impl.galoistools.gfDiv f g p).2
    r = [] ∨ refGfDegree r < refGfDegree g

/-- Small-dividend division: when `deg f < deg g`, division yields a zero
    quotient and `f` (stripped) as remainder — `gfDiv f g p = ([], refGfStrip f)`.
    Pins the base case of the recursion. Over `impl.galoistools.gfDiv`,
    `refGfDegree`, `refGfStrip`. -/
def spec_div_small (impl : RepoImpl) : Prop :=
  ∀ (f g : List Nat) (p : Nat), g ≠ [] → refGfDegree f < refGfDegree g →
    impl.galoistools.gfDiv f g p = ([], refGfStrip f)

/-- Remainder idempotence: reducing a remainder again by the same divisor changes
    nothing — `gfRem (gfRem f g p) g p = gfRem f g p` over a prime field for a
    nonempty `g`. The remainder is a fixed point of reduction. Over
    `impl.galoistools.gfRem`. -/
def spec_rem_idempotent (impl : RepoImpl) : Prop :=
  ∀ (f g : List Nat) (p : Nat), PrimeField p → g ≠ [] →
    impl.galoistools.gfRem (impl.galoistools.gfRem f g p) g p = impl.galoistools.gfRem f g p

-- ════════════════════════════════════════════════════════════════
-- gfGcd: divides both, monic, boundary
-- ════════════════════════════════════════════════════════════════

/-- GCD divides both inputs: for `p > 1` with normalized inputs and a unit-leading
    (monic) nonzero gcd, both `f` and `g` reduce to the zero polynomial modulo the
    gcd — `gfRem f (gfGcd f g p) p = [] ∧ gfRem g (gfGcd f g p) p = []`. This is
    the *common divisor* half of the gcd characterization, pinned via the frozen
    remainder. A degenerate `gfGcd := fun _ _ _ => [1]` fails whenever `f` or `g`
    has positive degree. Over `impl.galoistools.gfGcd`, `impl.galoistools.gfRem`. -/
def spec_gcd_divides_both (impl : RepoImpl) : Prop :=
  ∀ (f g : List Nat) (p : Nat), PrimeField p → IsNorm p f → IsNorm p g →
    impl.galoistools.gfRem f (impl.galoistools.gfGcd f g p) p = [] ∧
    impl.galoistools.gfRem g (impl.galoistools.gfGcd f g p) p = []

/-- GCD is monic (or zero): over a prime field with normalized inputs, the gcd is
    either the zero polynomial (only when both inputs are `[]`) or has leading
    coefficient `1` — `gfGcd f g p = [] ∨ refLeadCoeff (gfGcd f g p) = 1`. Pins the
    canonical monic normalization that makes the gcd unique. (Over a composite
    modulus the monic normalization can fail to reach leading coefficient `1` when
    that coefficient is a zero-divisor.) Over `impl.galoistools.gfGcd`,
    `refLeadCoeff`. -/
def spec_gcd_monic (impl : RepoImpl) : Prop :=
  ∀ (f g : List Nat) (p : Nat), PrimeField p → IsNorm p f → IsNorm p g →
    impl.galoistools.gfGcd f g p = [] ∨ refLeadCoeff (impl.galoistools.gfGcd f g p) = 1

/-- GCD with the zero polynomial: `gfGcd f [] p = (gfMonic f p).2` — the gcd of
    `f` and `0` is the monic associate of `f`. Boundary law pinning the Euclidean
    base case. Over `impl.galoistools.gfGcd`, `impl.galoistools.gfMonic`. -/
def spec_gcd_zero_right (impl : RepoImpl) : Prop :=
  ∀ (f : List Nat) (p : Nat), impl.galoistools.gfGcd f [] p = (impl.galoistools.gfMonic f p).2

/-- GCD is empty exactly at the double-zero input: for `p > 1` and normalized
    inputs, `gfGcd f g p = []` iff both `f = []` and `g = []`. Rules out a
    degenerate all-empty gcd. Over `impl.galoistools.gfGcd`. -/
def spec_gcd_empty_iff (impl : RepoImpl) : Prop :=
  ∀ (f g : List Nat) (p : Nat), 1 < p → IsNorm p f → IsNorm p g →
    (impl.galoistools.gfGcd f g p = [] ↔ (f = [] ∧ g = []))

/-- Self-gcd: for a normalized `f` over `p > 1`, `gfGcd f f p = (gfMonic f p).2` —
    the gcd of a polynomial with itself is its monic associate. This directly rules
    out a degenerate constant `gfGcd := fun _ _ _ => [1]`: for any `f` of positive
    degree, `gfMonic f p |>.2` has that degree, not `[1]`. Over
    `impl.galoistools.gfGcd`, `impl.galoistools.gfMonic`. -/
def spec_gcd_self (impl : RepoImpl) : Prop :=
  ∀ (f : List Nat) (p : Nat), 1 < p → IsNorm p f →
    impl.galoistools.gfGcd f f p = (impl.galoistools.gfMonic f p).2

/-- GCD maximality (greatestness): over a prime field with normalized inputs,
    every common divisor `d` of `f` and `g` also divides the gcd — if
    `gfRem f d p = []` and `gfRem g d p = []` then `gfRem (gfGcd f g p) d p = []`.
    This is the *greatest* half of the gcd characterization; paired with
    `spec_gcd_divides_both` it pins `gfGcd` to the genuine (monic) greatest common
    divisor, closing the reward-hack where a mere common divisor (or `[1]`) is
    returned. Over `impl.galoistools.gfGcd`, `impl.galoistools.gfRem`. -/
def spec_gcd_maximal (impl : RepoImpl) : Prop :=
  ∀ (f g d : List Nat) (p : Nat), PrimeField p → IsNorm p f → IsNorm p g → d ≠ [] →
    impl.galoistools.gfRem f d p = [] → impl.galoistools.gfRem g d p = [] →
    impl.galoistools.gfRem (impl.galoistools.gfGcd f g p) d p = []

-- ════════════════════════════════════════════════════════════════
-- gfPowMod: repeated-squaring modular exponentiation
-- ════════════════════════════════════════════════════════════════

/-- Zero exponent: `gfPowMod f 0 g p = [1]` — the empty product is the unit
    polynomial. Over `impl.galoistools.gfPowMod`. -/
def spec_powmod_zero (impl : RepoImpl) : Prop :=
  ∀ (f g : List Nat) (p : Nat), impl.galoistools.gfPowMod f 0 g p = [1]

/-- Modular-exponentiation recurrence: `f^(n+1) mod g = (f^n mod g · f) mod g` —
    `gfPowMod f (n+1) g p = gfRem (gfMul (gfPowMod f n g p) f p) g p`. This pins
    the repeated-squaring result to the genuine iterated modular product for every
    exponent, defeating a degenerate constant `gfPowMod`. Over
    `impl.galoistools.gfPowMod`, `impl.galoistools.gfRem`, `impl.galoistools.gfMul`. -/
def spec_powmod_recurrence (impl : RepoImpl) : Prop :=
  ∀ (f g : List Nat) (p n : Nat), PrimeField p →
    impl.galoistools.gfPowMod f (n + 1) g p =
      impl.galoistools.gfRem (impl.galoistools.gfMul (impl.galoistools.gfPowMod f n g p) f p) g p

/-- Modular-exponentiation reducedness: for a divisor `g` of positive degree, the
    result of `gfPowMod` is already reduced modulo `g` — reducing it again is the
    identity, `gfRem (gfPowMod f (n+1) g p) g p = gfPowMod f (n+1) g p`. (`n+1`
    positive so the result is a genuine remainder, not the `[1]` unit.) Over
    `impl.galoistools.gfPowMod`, `impl.galoistools.gfRem`, `refGfDegree`. -/
def spec_powmod_reduced (impl : RepoImpl) : Prop :=
  ∀ (f g : List Nat) (p n : Nat), PrimeField p → 0 < refGfDegree g →
    impl.galoistools.gfRem (impl.galoistools.gfPowMod f (n + 1) g p) g p =
      impl.galoistools.gfPowMod f (n + 1) g p

-- ════════════════════════════════════════════════════════════════
-- gfGcdex: extended-Euclid boundary laws (Bézout cofactor structure)
-- ════════════════════════════════════════════════════════════════

/-- Extended Euclid at the double-zero input: `gfGcdex [] [] p = ([1], [], [])` —
    the trivial Bézout identity `1·0 + 0·0 = 0` with the unit cofactor. Pins the
    base case of the extended-Euclid recursion. Over `impl.galoistools.gfGcdex`. -/
def spec_gcdex_both_empty (impl : RepoImpl) : Prop :=
  ∀ (p : Nat), impl.galoistools.gfGcdex [] [] p = ([1], [], [])

/-- Extended Euclid with a zero first argument: the returned gcd component (the
    third) is the monic associate of `g` — `(gfGcdex [] g p).2.2 = (gfMonic g p).2`
    — matching `gfGcd [] g p`. Pins the extended-Euclid boundary to the same monic
    normalization as the plain gcd. Over `impl.galoistools.gfGcdex`,
    `impl.galoistools.gfMonic`. -/
def spec_gcdex_left_zero_gcd (impl : RepoImpl) : Prop :=
  ∀ (g : List Nat) (p : Nat), g ≠ [] →
    (impl.galoistools.gfGcdex [] g p).2.2 = (impl.galoistools.gfMonic g p).2

/-- Bézout identity — the headline law for extended Euclid. Over a prime field with
    normalized inputs, writing `(s, t, h) = gfGcdex f g p`, the cofactors recompose the
    gcd: `s·f + t·g = h`, i.e. `gfAdd (gfMul s f p) (gfMul t g p) p = h`, AND that `h`
    is exactly the monic gcd `gfGcd f g p`. This is the defining property of the
    extended Euclidean algorithm — that `gfGcdex` returns genuine Bézout cofactors for
    the *same* gcd `gfGcd` computes, not merely a pair of boundary values. It defeats a
    degenerate `gfGcdex := fun _ _ _ => ([], [], [1])` (which fails the recomposition
    whenever the true gcd has positive degree) and any implementation whose third
    component drifts from `gfGcd`. (Primality is required: over a composite modulus a
    non-invertible leading coefficient breaks the cofactor arithmetic; normalization is
    required: leading-zero or unreduced inputs desynchronize the coefficient-list
    equality.) Over `impl.galoistools.gfGcdex`, `impl.galoistools.gfAdd`,
    `impl.galoistools.gfMul`, `impl.galoistools.gfGcd`. -/
def spec_gcdex_bezout (impl : RepoImpl) : Prop :=
  ∀ (f g : List Nat) (p : Nat), PrimeField p → IsNorm p f → IsNorm p g →
    let stt := impl.galoistools.gfGcdex f g p
    impl.galoistools.gfAdd (impl.galoistools.gfMul stt.1 f p)
        (impl.galoistools.gfMul stt.2.1 g p) p = stt.2.2 ∧
      stt.2.2 = impl.galoistools.gfGcd f g p

-- ════════════════════════════════════════════════════════════════
-- Quotient-ring structure: remainder is the reduction map GF(p)[x] → GF(p)[x]/(g)
-- ════════════════════════════════════════════════════════════════

/-- Additive congruence of the remainder: over a prime field, reducing a sum
    modulo `g` equals reducing the sum of the reduced summands —
    `gfRem (gfAdd a b p) g p = gfRem (gfAdd (gfRem a g p) (gfRem b g p) p) g p`.
    Pins `gfRem` as the additive reduction map onto the quotient ring
    `GF(p)[x]/(g)`. Over `impl.galoistools.gfRem`, `impl.galoistools.gfAdd`. -/
def spec_rem_add_congr (impl : RepoImpl) : Prop :=
  ∀ (a b g : List Nat) (p : Nat), PrimeField p → IsNorm p a → IsNorm p b → IsNorm p g → g ≠ [] →
    impl.galoistools.gfRem (impl.galoistools.gfAdd a b p) g p =
      impl.galoistools.gfRem
        (impl.galoistools.gfAdd (impl.galoistools.gfRem a g p)
          (impl.galoistools.gfRem b g p) p) g p

/-- Multiplicative congruence of the remainder: over a prime field, reducing a
    product modulo `g` equals reducing the product of the reduced factors —
    `gfRem (gfMul a b p) g p = gfRem (gfMul (gfRem a g p) (gfRem b g p) p) g p`.
    Pins `gfRem` as the multiplicative reduction map onto the quotient ring
    `GF(p)[x]/(g)`. Over `impl.galoistools.gfRem`, `impl.galoistools.gfMul`. -/
def spec_rem_mul_congr (impl : RepoImpl) : Prop :=
  ∀ (a b g : List Nat) (p : Nat), PrimeField p → IsNorm p a → IsNorm p b → IsNorm p g → g ≠ [] →
    impl.galoistools.gfRem (impl.galoistools.gfMul a b p) g p =
      impl.galoistools.gfRem
        (impl.galoistools.gfMul (impl.galoistools.gfRem a g p)
          (impl.galoistools.gfRem b g p) p) g p

/-- Coset invariance of the remainder: over a prime field, adding any multiple of
    `g` leaves the remainder unchanged —
    `gfRem (gfAdd f (gfMul q g p) p) g p = gfRem f g p` for every `q`. The
    remainder depends only on the coset of `f` modulo `g`. Over
    `impl.galoistools.gfRem`, `impl.galoistools.gfAdd`, `impl.galoistools.gfMul`. -/
def spec_rem_coset_invariant (impl : RepoImpl) : Prop :=
  ∀ (f g q : List Nat) (p : Nat), PrimeField p → IsNorm p f → IsNorm p g → g ≠ [] →
    impl.galoistools.gfRem (impl.galoistools.gfAdd f (impl.galoistools.gfMul q g p) p) g p =
      impl.galoistools.gfRem f g p

/-- Exact division reconstruction: over a prime field, when `f` is divisible by `g`
    (`gfRem f g p = []`), the quotient times `g` recovers `f` —
    `gfMul (gfQuo f g p) g p = f`. Pins the quotient as the genuine exact divisor in
    the divisible case. Over `impl.galoistools.gfMul`, `impl.galoistools.gfQuo`,
    `impl.galoistools.gfRem`. -/
def spec_exact_quo_mul (impl : RepoImpl) : Prop :=
  ∀ (f g : List Nat) (p : Nat), PrimeField p → IsNorm p f → IsNorm p g → g ≠ [] →
    impl.galoistools.gfRem f g p = [] →
    impl.galoistools.gfMul (impl.galoistools.gfQuo f g p) g p = f

/-- Evaluation reconstruction of the division identity: over a prime field, at any
    point `x` where `g` does not vanish, `f(x)` is recovered from the quotient and
    remainder evaluations — writing `(q, r) = gfDiv f g p`,
    `refPolyEval p f x = (refPolyEval p q x * refPolyEval p g x + refPolyEval p r x) % p`.
    The `f = q·g + r` identity read through the frozen evaluation homomorphism. Over
    `impl.galoistools.gfDiv`, `refPolyEval`. -/
def spec_div_eval_reconstruction (impl : RepoImpl) : Prop :=
  ∀ (f g : List Nat) (p x : Nat), PrimeField p → IsNorm p f → IsNorm p g → g ≠ [] →
    refPolyEval p g x ≠ 0 →
    let qr := impl.galoistools.gfDiv f g p
    refPolyEval p f x =
      (refPolyEval p qr.1 x * refPolyEval p g x + refPolyEval p qr.2 x) % p

-- ════════════════════════════════════════════════════════════════
-- gfGcd: commutativity, degree bound, root characterization
-- ════════════════════════════════════════════════════════════════

/-- GCD commutativity: over a prime field with normalized inputs the monic gcd is
    independent of argument order — `gfGcd f g p = gfGcd g f p`. Over
    `impl.galoistools.gfGcd`. -/
def spec_gcd_comm (impl : RepoImpl) : Prop :=
  ∀ (f g : List Nat) (p : Nat), PrimeField p → IsNorm p f → IsNorm p g →
    impl.galoistools.gfGcd f g p = impl.galoistools.gfGcd g f p

/-- GCD degree bound: over a prime field, for nonzero normalized inputs the monic
    gcd has degree no larger than either input —
    `refGfDegree (gfGcd f g p) ≤ refGfDegree f ∧ refGfDegree (gfGcd f g p) ≤ refGfDegree g`.
    A common divisor cannot exceed the size of what it divides. Over
    `impl.galoistools.gfGcd`, `refGfDegree`. -/
def spec_gcd_degree_le_inputs (impl : RepoImpl) : Prop :=
  ∀ (f g : List Nat) (p : Nat), PrimeField p → IsNorm p f → IsNorm p g → f ≠ [] → g ≠ [] →
    refGfDegree (impl.galoistools.gfGcd f g p) ≤ refGfDegree f ∧
      refGfDegree (impl.galoistools.gfGcd f g p) ≤ refGfDegree g

/-- GCD root characterization: over a prime field, a point `x` is a root of the
    monic gcd exactly when it is a common root of both inputs —
    `refPolyEval p (gfGcd f g p) x = 0 ↔ (refPolyEval p f x = 0 ∧ refPolyEval p g x = 0)`.
    Reads the gcd's divisibility structure through the frozen evaluation
    homomorphism. Over `impl.galoistools.gfGcd`, `refPolyEval`. -/
def spec_gcd_roots_common (impl : RepoImpl) : Prop :=
  ∀ (f g : List Nat) (p x : Nat), PrimeField p → IsNorm p f → IsNorm p g →
    (refPolyEval p (impl.galoistools.gfGcd f g p) x = 0 ↔
      (refPolyEval p f x = 0 ∧ refPolyEval p g x = 0))

/-- Extended-Euclid cofactor degree bounds: over a prime field, for positive-degree
    normalized inputs the returned Bézout cofactors are reduced — writing
    `(s, t, h) = gfGcdex f g p`, `refGfDegree s < refGfDegree g` and
    `refGfDegree t < refGfDegree f`. Pins the extended-Euclid output to the reduced
    cofactor pair (not merely any Bézout witnesses). Over `impl.galoistools.gfGcdex`,
    `refGfDegree`. -/
def spec_gcdex_cofactor_deg_bound (impl : RepoImpl) : Prop :=
  ∀ (f g : List Nat) (p : Nat), PrimeField p → IsNorm p f → IsNorm p g →
    0 < refGfDegree f → 0 < refGfDegree g →
    let stt := impl.galoistools.gfGcdex f g p
    refGfDegree stt.1 < refGfDegree g ∧ refGfDegree stt.2.1 < refGfDegree f

-- ════════════════════════════════════════════════════════════════
-- gfPowMod: exponent laws in the quotient ring
-- ════════════════════════════════════════════════════════════════

/-- Modular-exponentiation exponent additivity: over a prime field with a
    positive-degree divisor, powers add via the modular product —
    `gfPowMod f (m + n) g p = gfRem (gfMul (gfPowMod f m g p) (gfPowMod f n g p) p) g p`.
    Pins `gfPowMod` to a genuine homomorphism from the additive monoid of exponents
    into the multiplicative monoid of `GF(p)[x]/(g)`. Over
    `impl.galoistools.gfPowMod`, `impl.galoistools.gfRem`, `impl.galoistools.gfMul`,
    `refGfDegree`. -/
def spec_powmod_add_exponent (impl : RepoImpl) : Prop :=
  ∀ (f g : List Nat) (p m n : Nat), PrimeField p → IsNorm p f → IsNorm p g →
    0 < refGfDegree g →
    impl.galoistools.gfPowMod f (m + n) g p =
      impl.galoistools.gfRem
        (impl.galoistools.gfMul (impl.galoistools.gfPowMod f m g p)
          (impl.galoistools.gfPowMod f n g p) p) g p

/-- Modular-exponentiation exponent multiplicativity: over a prime field with a
    positive-degree divisor, iterating a power exponentiates the exponent —
    `gfPowMod f (m * n) g p = gfPowMod (gfPowMod f m g p) n g p`. The nested
    power-of-a-power law in the quotient ring `GF(p)[x]/(g)`. Over
    `impl.galoistools.gfPowMod`, `refGfDegree`. -/
def spec_powmod_mul_exponent (impl : RepoImpl) : Prop :=
  ∀ (f g : List Nat) (p m n : Nat), PrimeField p → IsNorm p f → IsNorm p g →
    0 < refGfDegree g →
    impl.galoistools.gfPowMod f (m * n) g p =
      impl.galoistools.gfPowMod (impl.galoistools.gfPowMod f m g p) n g p

/-- Frobenius additivity in the quotient ring: over a prime field of characteristic
    `p` with a positive-degree divisor, the `p`-th power of a sum reduces to the sum
    of the `p`-th powers —
    `gfPowMod (gfAdd a b p) p g p = gfRem (gfAdd (gfPowMod a p g p) (gfPowMod b p g p) p) g p`.
    The Frobenius endomorphism `x ↦ x^p` is additive over `GF(p)`. Over
    `impl.galoistools.gfPowMod`, `impl.galoistools.gfAdd`, `impl.galoistools.gfRem`,
    `refGfDegree`. -/
def spec_powmod_frobenius (impl : RepoImpl) : Prop :=
  ∀ (a b g : List Nat) (p : Nat), PrimeField p → IsNorm p a → IsNorm p b → IsNorm p g →
    0 < refGfDegree g →
    impl.galoistools.gfPowMod (impl.galoistools.gfAdd a b p) p g p =
      impl.galoistools.gfRem
        (impl.galoistools.gfAdd (impl.galoistools.gfPowMod a p g p)
          (impl.galoistools.gfPowMod b p g p) p) g p
