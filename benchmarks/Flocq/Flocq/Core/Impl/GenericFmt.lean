import Flocq.Core.Impl.Raux
import Flocq.Core.Impl.Defs

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Flocq.Core.Impl.GenericFmt

Generic floating-point format and rounding, translated from
`src/Core/Generic_fmt.v`.

This module defines what it means for a real number to be in generic
floating-point format, and provides the main `round` function that maps
an arbitrary real to its nearest representable value.

Key definitions (spec helpers, fixed vocabulary):
- `cexp beta fexp x` — canonical exponent: `fexp (mag beta x)`
- `scaledMantissa beta fexp x` — scaled mantissa: `x * beta^(-cexp x)`
- `genericFormat beta fexp x` — `x` is representable in the format
- `genericCanonical beta fexp f` — a `FloatNum` is in canonical form
- `Znearest choice x` — round to nearest integer with tie-breaking

Key API:
- `round beta fexp rnd x` — round `x` to the nearest format value

Types and signatures are fixed vocabulary (DO NOT MODIFY).
Implement only the `round` function body.
-/

-- ── Core types (DO NOT MODIFY) ───────────────────────────────────────────────

/-- `ValidExp fexp`: asserts that `fexp : Int → Int` is a valid floating-point
    exponent function.  For every integer `k`:
    - If `fexp(k) < k` then `fexp(k+1) ≤ k` (no overflow in the normal region).
    - If `k ≤ fexp(k)` (subnormal region) then `fexp(fexp(k)+1) ≤ fexp(k)` and
      `fexp` is constant on `(-∞, fexp(k)]`.
    Mirrors Coq's `Valid_exp` class from `src/Core/Generic_fmt.v`. -/
class ValidExp (fexp : Int → Int) : Prop where
  h : ∀ k : Int,
    (fexp k < k → fexp (k + 1) ≤ k) ∧
    (k ≤ fexp k →
      fexp (fexp k + 1) ≤ fexp k ∧
      ∀ l : Int, l ≤ fexp k → fexp l = fexp k)

/-- `MonotoneExp fexp`: asserts that `fexp : Int → Int` is monotone.
    Mirrors Coq's `Monotone_exp` from `src/Core/Generic_fmt.v`. -/
class MonotoneExp (fexp : Int → Int) : Prop where
  h : ∀ ex ey : Int, ex ≤ ey → fexp ex ≤ fexp ey

/-- `ValidRnd rnd`: asserts that `rnd : ℝ → Int` is a valid rounding function:
    monotone and the identity on integers.
    Mirrors Coq's `Valid_rnd` from `src/Core/Round_pred.v`. -/
class ValidRnd (rnd : ℝ → Int) : Prop where
  le  : ∀ x y : ℝ, x ≤ y → rnd x ≤ rnd y
  IZR : ∀ n : Int, rnd (n : ℝ) = n

-- ── Spec helpers (DO NOT MODIFY) ─────────────────────────────────────────────

/-- Convert a float record to a real number: `Fnum * beta^Fexp`.
    Mirrors Coq's `F2R` from `src/Core/Defs.v`. -/
noncomputable def F2R (beta : Radix) (f : FloatNum) : ℝ :=
  (f.Fnum : ℝ) * Flocq.bpow beta f.Fexp

/-- Round-to-nearest point: `f` is in format `F` and minimises `|f - x|`.
    Mirrors Coq's `Rnd_N_pt` from `src/Core/Round_pred.v`. -/
def RndNPt (F : ℝ → Prop) (x f : ℝ) : Prop :=
  F f ∧ ∀ g : ℝ, F g → |f - x| ≤ |g - x|

/-- Round to nearest integer; when equidistant, use `choice n = true` to
    select the larger value `Zceil x`, `false` for `Zfloor x`.
    Mirrors Coq's `Znearest` from `src/Core/Round_NE.v`. -/
noncomputable def Znearest (choice : Int → Bool) (x : ℝ) : Int :=
  match Rcompare (x - (Zfloor x : ℝ)) (1 / 2) with
  | Ordering.lt => Zfloor x
  | Ordering.eq => if choice (Zfloor x) then Zceil x else Zfloor x
  | Ordering.gt => Zceil x

/-- Canonical exponent: `fexp` applied to the magnitude of `x`.
    This is the exponent that a canonical float representing `x` would have.
    Mirrors Coq's `cexp` from `src/Core/Generic_fmt.v`. -/
noncomputable def cexp (beta : Radix) (fexp : Int → Int) (x : ℝ) : Int :=
  fexp (Flocq.mag beta x)

/-- Scaled mantissa: `x * beta^(-cexp(x))`.
    When `x` is in generic format, `Ztrunc(scaledMantissa x)` is the integer
    mantissa. Mirrors Coq's `scaled_mantissa`. -/
noncomputable def scaledMantissa (beta : Radix) (fexp : Int → Int) (x : ℝ) : ℝ :=
  x * Flocq.bpow beta (-(cexp beta fexp x))

/-- `x` is in generic format iff it equals `F2R` of its canonically-rounded
    scaled mantissa. Mirrors Coq's `generic_format`. -/
noncomputable def genericFormat (beta : Radix) (fexp : Int → Int) (x : ℝ) : Prop :=
  x = F2R beta ⟨Ztrunc (scaledMantissa beta fexp x), cexp beta fexp x⟩

/-- A `FloatNum` is canonical if its stored exponent equals `cexp` of its
    real value. Mirrors Coq's `canonical`. -/
def genericCanonical (beta : Radix) (fexp : Int → Int) (f : FloatNum) : Prop :=
  f.Fexp = cexp beta fexp (F2R beta f)

-- ── ValidRnd instances (axiomatized — proofs require real-analysis) ──────────

/-- `Zfloor` is a valid rounding function (monotone and integer-idempotent). -/
axiom ZfloorValidRnd : ValidRnd Zfloor

instance : ValidRnd Zfloor := ZfloorValidRnd

/-- `Zceil` is a valid rounding function (monotone and integer-idempotent). -/
axiom ZceilValidRnd : ValidRnd Zceil

instance : ValidRnd Zceil := ZceilValidRnd

/-- `Znearest choice` is a valid rounding function for any choice function. -/
axiom ZnearestValidRnd (choice : Int → Bool) : ValidRnd (Znearest choice)

instance (choice : Int → Bool) : ValidRnd (Znearest choice) :=
  ZnearestValidRnd choice

-- ── Additional spec-helper axioms (DO NOT MODIFY) ────────────────────────────

/-- Every number in generic format has a canonical float representation. -/
axiom canonicalGenericFormat : ∀ (beta : Radix) (fexp : Int → Int) (x : ℝ),
  genericFormat beta fexp x →
  ∃ f : FloatNum, x = F2R beta f ∧ genericCanonical beta fexp f

/-- `cexp(-x) = cexp(x)` — the canonical exponent is symmetric. -/
axiom cexpOpp : ∀ (beta : Radix) (fexp : Int → Int) (x : ℝ),
  cexp beta fexp (-x) = cexp beta fexp x

/-- The ceil mantissa of a small positive `x` (where `ex ≤ fexp ex`) equals 1. -/
axiom mantissaUPSmallPos : ∀ (beta : Radix) (fexp : Int → Int) (x : ℝ) (ex : Int),
  Flocq.bpow beta (ex - 1) ≤ x → x < Flocq.bpow beta ex →
  ex ≤ fexp ex → Zceil (x * Flocq.bpow beta (-(fexp ex))) = 1

/-- The scaled mantissa of a small positive `x` lies strictly in `(0, 1)`. -/
axiom mantissaSmallPos : ∀ (beta : Radix) (fexp : Int → Int) (x : ℝ) (ex : Int),
  Flocq.bpow beta (ex - 1) ≤ x → x < Flocq.bpow beta ex →
  ex ≤ fexp ex →
  (0 : ℝ) < x * Flocq.bpow beta (-(fexp ex)) ∧
  x * Flocq.bpow beta (-(fexp ex)) < (1 : ℝ)

namespace Flocq

-- ── API signatures (DO NOT MODIFY) ───────────────────────────────────────────

/-- Signature for the generic rounding function. -/
abbrev RoundSig := Radix → (Int → Int) → (ℝ → Int) → ℝ → ℝ

/-- Signature for nearest-integer rounding with tie-breaking choice. -/
abbrev ZnearestSig := (Int → Bool) → ℝ → Int

end Flocq

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- !benchmark @start code_aux def=znearest
-- !benchmark @end code_aux def=znearest

noncomputable def Flocq.znearest : Flocq.ZnearestSig :=
-- !benchmark @start code def=znearest
  fun choice x => Znearest choice x
-- !benchmark @end code def=znearest


/-- Generic rounding function: compute `F2R(rnd(scaledMantissa(x)), cexp(x))`.
    This maps any real `x` to the nearest representable floating-point value
    under exponent function `fexp`, using rounding direction `rnd`.
    Mirrors Coq's `round` from `src/Core/Generic_fmt.v`. -/
noncomputable def Flocq.round : Flocq.RoundSig :=
  fun beta fexp rnd x =>
    F2R beta ⟨rnd (scaledMantissa beta fexp x), cexp beta fexp x⟩

-- ── Post-round spec-helper axioms (reference Flocq.round, DO NOT MODIFY) ─────

/-- If `x ∈ (beta^(ex-1), beta^ex)` and the rounded value is 0,
    then `ex ≤ fexp ex`. -/
axiom expSmallRound0Pos : ∀ (beta : Radix) (fexp : Int → Int) [ValidExp fexp]
  (rnd : ℝ → Int) [ValidRnd rnd] (x : ℝ) (ex : Int),
  Flocq.bpow beta (ex - 1) ≤ x → x < Flocq.bpow beta ex →
  Flocq.round beta fexp rnd x = 0 → ex ≤ fexp ex

/-- If the round-down of `x` is positive, it has the same magnitude as `x`. -/
axiom magDN : ∀ (beta : Radix) (fexp : Int → Int) [ValidExp fexp] (x : ℝ),
  (0 : ℝ) < Flocq.round beta fexp Zfloor x →
  Flocq.mag beta (Flocq.round beta fexp Zfloor x) = Flocq.mag beta x

/-- Round-up of a small positive `x` (where `ex ≤ fexp ex`) equals `beta^fexp(ex)`. -/
axiom roundUPSmallPos : ∀ (beta : Radix) (fexp : Int → Int) [ValidExp fexp]
  (x : ℝ) (ex : Int),
  Flocq.bpow beta (ex - 1) ≤ x → x < Flocq.bpow beta ex →
  ex ≤ fexp ex →
  Flocq.round beta fexp Zceil x = Flocq.bpow beta (fexp ex)
