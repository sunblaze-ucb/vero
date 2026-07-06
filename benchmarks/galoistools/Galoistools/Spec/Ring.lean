import Galoistools.Harness

/-!
# Galoistools.Spec.Ring

Specifications for the `GF(p)[x]` ring operations `gfAdd`, `gfSub`, `gfMul`,
`gfNeg`, `gfMonic`. Each `spec_*` is a property over an arbitrary
`impl : RepoImpl`, reaching an API through `impl.galoistools.<fn>`.

Polynomials are big-endian coefficient lists over `GF(p)` (head = leading
coeff, `[]` = zero polynomial). The reference semantics below are stated against
frozen **Spec-local** helpers — `refGfStrip`, `refGfDegree`, `refLeadCoeff`,
`refGfTrunc`, `refPolyEval` — defined entirely within this Spec file (see the
"self-contained frozen reference helpers" note). `refPolyEval p f x` evaluates
`f` at `x` in `GF(p)` (the ring homomorphism `GF(p)[x] → GF(p)`); the ring laws
that would be awkward as raw coefficient-list equalities (associativity,
distributivity) are pinned semantically through `refPolyEval`, which is sound and
non-vacuous because `refPolyEval` is the genuine (frozen) evaluation map.

A polynomial is *normalized* (`IsNorm`) when it carries no leading zeros and all
coefficients are already reduced modulo `p`, i.e. `refGfTrunc p f = f` — SymPy's
standing precondition on `GF(p)[x]` inputs.

DO NOT MODIFY.
-/

namespace Galoistools

/-!
## Self-contained frozen reference helpers

The reference predicates and evaluation map below are rebuilt from `ref*` helpers
defined **entirely within this Spec file**, deliberately NOT reusing the
implementation helpers (`gfStrip`, `gfDegree`, `leadCoeff`, `gfTrunc`, `polyEval`,
…) from `Impl/Ring.lean`. Those implementation helpers live inside agent-editable
`!benchmark` slots (`global_aux` / `code_aux`); in `codeproof` mode the sandbox
empties those slots and lets the candidate re-supply them. If the specifications
depended on them, a candidate could redefine `polyEval := fun _ _ _ => 0` (making
the multiplicative evaluation-homomorphism laws hold vacuously, `0 = 0`), or
`gfTrunc := fun _ _ => []` (collapsing `IsNorm` so every normalized-input law is
vacuous), or `leadCoeff := fun _ => 1` (gaming the monic / gcd / division laws),
and pass every spec without doing the real work. Anchoring the specs to these
Spec-local, frozen copies makes the benchmark non-hackable: the reference
semantics are fixed no matter what the candidate supplies for the implementation
helpers. Each `ref*` helper is a byte-for-byte copy of the corresponding frozen
`Impl/Ring.lean` helper, so the reference semantics are identical to the intended
ones.
-/

/-- `refGfStrip f`: drop leading zeros from a big-endian coeff list. Frozen
    Spec-local copy of `Impl/Ring.gfStrip`. -/
def refGfStrip : List Nat → List Nat
  | [] => []
  | a :: as => if a = 0 then refGfStrip as else a :: as

/-- `refGfDegree f = len f - 1` as an `Int` (so `-1` for the zero polynomial).
    Frozen Spec-local copy of `Impl/Ring.gfDegree`. -/
def refGfDegree (f : List Nat) : Int := (f.length : Int) - 1

/-- `refLeadCoeff f`: the leading coefficient `f[0]`, or `0` for `f = []`. Frozen
    Spec-local copy of `Impl/Ring.leadCoeff`. -/
def refLeadCoeff (f : List Nat) : Nat :=
  match f with
  | [] => 0
  | a :: _ => a

/-- `refGfTrunc p f`: reduce every coefficient modulo `p`, then strip leading
    zeros. Frozen Spec-local copy of `Impl/Ring.gfTrunc`. -/
def refGfTrunc (p : Nat) (f : List Nat) : List Nat :=
  refGfStrip (f.map (· % p))

/-- `refPolyEvalRevAux p x l`: little-endian Horner over `l`. Frozen Spec-local
    copy of `Impl/Ring.polyEvalRevAux`. -/
def refPolyEvalRevAux (p x : Nat) : List Nat → Nat
  | [] => 0
  | c :: cs => (c + x * refPolyEvalRevAux p x cs) % p

/-- `refPolyEval p f x`: evaluate the big-endian polynomial `f` (head = leading
    coefficient) at the point `x` in `GF(p)`. Frozen Spec-local copy of
    `Impl/Ring.polyEval` — the genuine ring homomorphism `GF(p)[x] → GF(p)` at
    `x`, against which the multiplicative ring laws are stated. -/
def refPolyEval (p : Nat) (f : List Nat) (x : Nat) : Nat :=
  refPolyEvalRevAux p x f.reverse

/-- `IsNorm p f`: `f` is a normalized `GF(p)[x]` polynomial — stripped of leading
    zeros with all coefficients reduced modulo `p`, i.e. `refGfTrunc p f = f`.
    Frozen predicate stated against the Spec-local `refGfTrunc`; SymPy's standing
    precondition on `GF(p)[x]` inputs. -/
def IsNorm (p : Nat) (f : List Nat) : Prop := refGfTrunc p f = f

/-- `PrimeField p`: `p` is a prime modulus, so `GF(p)` is a genuine field in which
    every nonzero residue is invertible. Stated mathlib-free as `1 < p` together
    with trial-division primality (`p` has no divisor `d` with `2 ≤ d < p`). SymPy
    requires the modulus of `GF(p)[x]` to be prime for division / gcd / modular
    exponentiation to be well-defined; the field laws below carry this as a
    hypothesis exactly where a non-invertible leading coefficient would break them.
    Frozen predicate. -/
def PrimeField (p : Nat) : Prop := 1 < p ∧ ∀ d, 2 ≤ d → d < p → p % d ≠ 0

end Galoistools

open Galoistools

-- ════════════════════════════════════════════════════════════════
-- Additive structure: commutative group over GF(p)
-- ════════════════════════════════════════════════════════════════

/-- Additive identity: adding the zero polynomial `[]` leaves a normalized `f`
    unchanged — `gfAdd f [] p = f`. Over `impl.galoistools.gfAdd`. -/
def spec_add_zero (impl : RepoImpl) : Prop :=
  ∀ (f : List Nat) (p : Nat), IsNorm p f → impl.galoistools.gfAdd f [] p = f

/-- Additive commutativity: `gfAdd f g p = gfAdd g f p` for all polynomials.
    A raw coefficient-list equality (holds for arbitrary inputs). Over
    `impl.galoistools.gfAdd`. -/
def spec_add_comm (impl : RepoImpl) : Prop :=
  ∀ (f g : List Nat) (p : Nat), impl.galoistools.gfAdd f g p = impl.galoistools.gfAdd g f p

/-- Additive associativity (semantic): the two bracketings of a three-fold sum
    agree as functions on `GF(p)` at every point, for `p > 1`. Anchored through
    the frozen `refPolyEval` (the evaluation homomorphism) so the law is captured
    soundly without the leading-zero bookkeeping of a raw list equality. Over
    `refPolyEval`, `impl.galoistools.gfAdd`. -/
def spec_add_assoc_eval (impl : RepoImpl) : Prop :=
  ∀ (f g h : List Nat) (p x : Nat), 1 < p →
    refPolyEval p (impl.galoistools.gfAdd (impl.galoistools.gfAdd f g p) h p) x =
      refPolyEval p (impl.galoistools.gfAdd f (impl.galoistools.gfAdd g h p) p) x

/-- Additive inverse: `gfAdd f (gfNeg f p) p = []` for `p > 1` — every polynomial
    cancels with its coefficient-wise negation to the zero polynomial. This pins
    `gfNeg` as the genuine additive inverse (a degenerate `gfNeg := id` fails).
    Over `impl.galoistools.gfAdd`, `impl.galoistools.gfNeg`. -/
def spec_add_neg_cancel (impl : RepoImpl) : Prop :=
  ∀ (f : List Nat) (p : Nat), 1 < p → impl.galoistools.gfAdd f (impl.galoistools.gfNeg f p) p = []

/-- Subtraction is addition of the negation: `gfSub f g p = gfAdd f (gfNeg g p) p`
    for `p > 1`. Ties the two frozen operations together. Over
    `impl.galoistools.gfSub`, `impl.galoistools.gfAdd`, `impl.galoistools.gfNeg`. -/
def spec_sub_eq_add_neg (impl : RepoImpl) : Prop :=
  ∀ (f g : List Nat) (p : Nat), 1 < p →
    impl.galoistools.gfSub f g p = impl.galoistools.gfAdd f (impl.galoistools.gfNeg g p) p

-- ════════════════════════════════════════════════════════════════
-- Multiplicative structure: pinned semantically via polyEval
-- ════════════════════════════════════════════════════════════════

/-- Multiplicative identity: `gfMul f [1] p = f` for normalized `f` with `p > 1`.
    A raw coefficient-list equality pinning `[1]` as the unit. Over
    `impl.galoistools.gfMul`. -/
def spec_mul_one (impl : RepoImpl) : Prop :=
  ∀ (f : List Nat) (p : Nat), 1 < p → IsNorm p f → impl.galoistools.gfMul f [1] p = f

/-- Multiplicative absorption: `gfMul f [] p = []` — multiplying by the zero
    polynomial gives the zero polynomial. Over `impl.galoistools.gfMul`. -/
def spec_mul_zero (impl : RepoImpl) : Prop :=
  ∀ (f : List Nat) (p : Nat), impl.galoistools.gfMul f [] p = []

/-- Degree additivity of the product: over a prime field, the degree of the
    product of two nonzero normalized polynomials is the sum of their degrees —
    `refGfDegree (gfMul f g p) = refGfDegree f + refGfDegree g`. This pins
    `GF(p)[x]` as an integral domain at the coefficient-list level (the leading
    terms never cancel). (Over a composite modulus a product of zero-divisor
    leading coefficients can drop the degree.) Over `impl.galoistools.gfMul`,
    `refGfDegree`. -/
def spec_mul_degree_add (impl : RepoImpl) : Prop :=
  ∀ (f g : List Nat) (p : Nat), PrimeField p → IsNorm p f → IsNorm p g → f ≠ [] → g ≠ [] →
    refGfDegree (impl.galoistools.gfMul f g p) = refGfDegree f + refGfDegree g

/-- No zero divisors: over a prime field, a product of normalized polynomials is
    the zero polynomial exactly when one of the factors is —
    `gfMul f g p = [] ↔ (f = [] ∨ g = [])`. The integral-domain law for
    `GF(p)[x]`. (Fails over a composite modulus, where two nonzero polynomials
    with zero-divisor leading coefficients can multiply to `[]`.) Over
    `impl.galoistools.gfMul`. -/
def spec_mul_zero_iff (impl : RepoImpl) : Prop :=
  ∀ (f g : List Nat) (p : Nat), PrimeField p → IsNorm p f → IsNorm p g →
    (impl.galoistools.gfMul f g p = [] ↔ (f = [] ∨ g = []))

/-- Evaluation homomorphism for multiplication: for `p > 1`, `gfMul` evaluated at
    any point `x` equals the product of the factor evaluations in `GF(p)` —
    `refPolyEval p (gfMul f g p) x = (refPolyEval p f x * refPolyEval p g x) % p`.
    This is the defining ring-homomorphism property of polynomial multiplication;
    it pins `gfMul` to the genuine convolution product at every field point,
    measured by the frozen `refPolyEval`. Over `impl.galoistools.gfMul`,
    `refPolyEval`, `%`. -/
def spec_mul_eval_hom (impl : RepoImpl) : Prop :=
  ∀ (f g : List Nat) (p x : Nat), 1 < p →
    refPolyEval p (impl.galoistools.gfMul f g p) x =
      (refPolyEval p f x * refPolyEval p g x) % p

/-- Evaluation homomorphism for subtraction: for `p > 1`, `gfSub` evaluated at any
    point `x` equals the difference of the factor evaluations in `GF(p)` —
    `refPolyEval p (gfSub f g p) x = (refPolyEval p f x + p - refPolyEval p g x % p) % p`.
    Pins `gfSub` to the genuine coefficient-wise difference at every field point,
    measured by the frozen `refPolyEval`. Over `impl.galoistools.gfSub`,
    `refPolyEval`, `%`. -/
def spec_sub_eval_hom (impl : RepoImpl) : Prop :=
  ∀ (f g : List Nat) (p x : Nat), 1 < p →
    refPolyEval p (impl.galoistools.gfSub f g p) x =
      (refPolyEval p f x + p - refPolyEval p g x % p) % p

/-- Multiplicative commutativity (semantic): `gfMul f g p` and `gfMul g f p`
    agree as functions on `GF(p)` at every point, for `p > 1`. Over
    `impl.galoistools.gfMul`, `refPolyEval`. -/
def spec_mul_comm_eval (impl : RepoImpl) : Prop :=
  ∀ (f g : List Nat) (p x : Nat), 1 < p →
    refPolyEval p (impl.galoistools.gfMul f g p) x =
      refPolyEval p (impl.galoistools.gfMul g f p) x

/-- Multiplicative associativity (semantic): the two bracketings of a triple
    product agree at every point of `GF(p)`, for `p > 1` — over `refPolyEval` and
    `impl.galoistools.gfMul`. Anchored semantically because raw list equality of
    the two associated products is a heavy structural fact; evaluation captures
    the ring law soundly. -/
def spec_mul_assoc_eval (impl : RepoImpl) : Prop :=
  ∀ (f g h : List Nat) (p x : Nat), 1 < p →
    refPolyEval p (impl.galoistools.gfMul (impl.galoistools.gfMul f g p) h p) x =
      refPolyEval p (impl.galoistools.gfMul f (impl.galoistools.gfMul g h p) p) x

/-- Distributivity (semantic): `f·(g + h) = f·g + f·h` as functions on `GF(p)`,
    for `p > 1` — over `refPolyEval`, `impl.galoistools.gfMul`,
    `impl.galoistools.gfAdd`. -/
def spec_mul_add_distrib_eval (impl : RepoImpl) : Prop :=
  ∀ (f g h : List Nat) (p x : Nat), 1 < p →
    refPolyEval p (impl.galoistools.gfMul f (impl.galoistools.gfAdd g h p) p) x =
      refPolyEval p (impl.galoistools.gfAdd (impl.galoistools.gfMul f g p)
                    (impl.galoistools.gfMul f h p) p) x

-- ════════════════════════════════════════════════════════════════
-- gfMonic: leading-coefficient normalizer
-- ════════════════════════════════════════════════════════════════

/-- Monic output: for a nonempty `f` with `p > 1` and leading coefficient coprime
    to `p`, the monic associate `(gfMonic f p).2` has leading coefficient `1`.
    Pins `gfMonic` to producing a genuinely monic polynomial, measured by the
    frozen `refLeadCoeff`. Over `impl.galoistools.gfMonic`, `refLeadCoeff`. -/
def spec_monic_leadCoeff_one (impl : RepoImpl) : Prop :=
  ∀ (f : List Nat) (p : Nat), 1 < p → f ≠ [] → Nat.gcd (refLeadCoeff f) p = 1 →
    refLeadCoeff (impl.galoistools.gfMonic f p).2 = 1

/-- Monic on a unit-leading input is the identity list: if `refLeadCoeff f = 1`
    then `gfMonic f p = (1, f)` — an already-monic polynomial is returned
    unchanged. Over `impl.galoistools.gfMonic`, `refLeadCoeff`. -/
def spec_monic_already (impl : RepoImpl) : Prop :=
  ∀ (f : List Nat) (p : Nat), f ≠ [] → refLeadCoeff f = 1 →
    impl.galoistools.gfMonic f p = (1, f)

/-- Monic normalization is multiplicative: over a prime field, the monic
    associate of a product of nonzero normalized polynomials equals the product of
    the monic associates — `(gfMonic (gfMul f g p) p).2 = gfMul (gfMonic f p).2 (gfMonic g p).2 p`.
    This pins `gfMonic` to a genuine scaling by the inverse leading coefficient
    (which is multiplicative), tying the leading-coefficient normalizer to the ring
    product. Over `impl.galoistools.gfMonic`, `impl.galoistools.gfMul`. -/
def spec_monic_mul_associate (impl : RepoImpl) : Prop :=
  ∀ (f g : List Nat) (p : Nat), PrimeField p → IsNorm p f → IsNorm p g → f ≠ [] → g ≠ [] →
    (impl.galoistools.gfMonic (impl.galoistools.gfMul f g p) p).2 =
      impl.galoistools.gfMul (impl.galoistools.gfMonic f p).2 (impl.galoistools.gfMonic g p).2 p
