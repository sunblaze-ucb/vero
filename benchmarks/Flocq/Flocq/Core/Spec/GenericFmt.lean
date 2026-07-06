import Flocq.Harness
import Flocq.Core.Impl.GenericFmt

open Flocq

/-!
# Flocq.Core.Spec.GenericFmt

Specifications for the generic floating-point format and rounding function
defined in `Impl/Core.GenericFmt.lean`, corresponding to key theorems from
`src/Core/Generic_fmt.v`.

The specs cover:
- `Znearest` negation symmetry
- Closure of the generic format under `F2R`, canonical floats, negation, and `round`
- Format inclusion when exponent functions are ordered
- Rounding to nearest satisfies the `RndNPt` predicate
- Rounding is monotone
- If already in format, rounding is the identity
- Rounding lies in a binade when the input does
- Every rounding equals either round-down or round-up

All specs access the `round` API via `impl.flocq.round` through `RepoImpl`.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- `znearest` exposes the shared nearest-integer rounding helper. -/
def spec_znearest_def (impl : RepoImpl) : Prop :=
  ∀ (choice : Int → Bool) (x : ℝ),
    impl.flocq.znearest choice x = Znearest choice x

/-- Znearest with a flipped choice function negates:
    `Znearest(choice, -x) = -Znearest(choice', x)`. -/
def spec_Znearest_opp (impl : RepoImpl) : Prop :=
  ∀ (choice : Int → Bool) (x : ℝ),
  Znearest choice (-x) = -(Znearest (fun t => !choice (-(t + 1))) x)

/-- F2R of a float in canonical position is in generic format. -/
def spec_generic_format_F2R (impl : RepoImpl) : Prop :=
  ∀ (beta : Radix) (fexp : Int → Int) [ValidExp fexp] (m e : Int),
  (m ≠ 0 → cexp beta fexp (F2R beta ⟨m, e⟩) ≤ e) →
  genericFormat beta fexp (F2R beta ⟨m, e⟩)

/-- F2R of a canonical float is in generic format. -/
def spec_generic_format_canonical (impl : RepoImpl) : Prop :=
  ∀ (beta : Radix) (fexp : Int → Int) [ValidExp fexp] (f : FloatNum),
  genericCanonical beta fexp f → genericFormat beta fexp (F2R beta f)

/-- If x is in generic format then so is -x. -/
def spec_generic_format_opp (impl : RepoImpl) : Prop :=
  ∀ (beta : Radix) (fexp : Int → Int) [ValidExp fexp] (x : ℝ),
  genericFormat beta fexp x → genericFormat beta fexp (-x)

/-- The result of rounding is always in generic format. -/
def spec_generic_format_round (impl : RepoImpl) : Prop :=
  ∀ (beta : Radix) (fexp : Int → Int) [ValidExp fexp]
  (rnd : ℝ → Int) [ValidRnd rnd] (x : ℝ),
  genericFormat beta fexp (impl.flocq.round beta fexp rnd x)

/-- If fexp2 ≤ fexp1 at mag(x), a format-1 number is also in format-2. -/
def spec_generic_inclusion_mag (impl : RepoImpl) : Prop :=
  ∀ (beta : Radix) (fexp1 fexp2 : Int → Int) [ValidExp fexp1] [ValidExp fexp2] (x : ℝ),
  (x ≠ 0 → fexp2 (Flocq.mag beta x) ≤ fexp1 (Flocq.mag beta x)) →
  genericFormat beta fexp1 x → genericFormat beta fexp2 x

/-- Any rounding mode rounds to either the round-down or round-up value. -/
def spec_round_DN_or_UP (impl : RepoImpl) : Prop :=
  ∀ (beta : Radix) (fexp : Int → Int) [ValidExp fexp]
  (rnd : ℝ → Int) [ValidRnd rnd] (x : ℝ),
  impl.flocq.round beta fexp rnd x = impl.flocq.round beta fexp Zfloor x ∨
  impl.flocq.round beta fexp rnd x = impl.flocq.round beta fexp Zceil x

/-- Rounding to nearest with a flipped tie-breaking function commutes with negation. -/
def spec_round_N_opp (impl : RepoImpl) : Prop :=
  ∀ (beta : Radix) (fexp : Int → Int) [ValidExp fexp]
  (choice : Int → Bool) (x : ℝ),
  impl.flocq.round beta fexp (Znearest choice) (-x) =
  -(impl.flocq.round beta fexp (Znearest (fun t => !choice (-(t + 1)))) x)

/-- Rounding to nearest satisfies the round-to-nearest-point predicate. -/
def spec_round_N_pt (impl : RepoImpl) : Prop :=
  ∀ (beta : Radix) (fexp : Int → Int) [ValidExp fexp]
  (choice : Int → Bool) (x : ℝ),
  RndNPt (genericFormat beta fexp) x (impl.flocq.round beta fexp (Znearest choice) x)

/-- A positive x in (beta^(ex-1), beta^ex) with fexp(ex) < ex rounds into
    [beta^(ex-1), beta^ex]. -/
def spec_round_bounded_large_pos (impl : RepoImpl) : Prop :=
  ∀ (beta : Radix) (fexp : Int → Int) [ValidExp fexp]
  (rnd : ℝ → Int) [ValidRnd rnd] (x : ℝ) (ex : Int),
  fexp ex < ex →
  Flocq.bpow beta (ex - 1) ≤ x → x < Flocq.bpow beta ex →
  Flocq.bpow beta (ex - 1) ≤ impl.flocq.round beta fexp rnd x ∧
  impl.flocq.round beta fexp rnd x ≤ Flocq.bpow beta ex

/-- Rounding a value already in generic format is the identity. -/
def spec_round_generic (impl : RepoImpl) : Prop :=
  ∀ (beta : Radix) (fexp : Int → Int) [ValidExp fexp]
  (rnd : ℝ → Int) [ValidRnd rnd] (x : ℝ),
  genericFormat beta fexp x → impl.flocq.round beta fexp rnd x = x

/-- Rounding is monotone: x ≤ y implies round(x) ≤ round(y). -/
def spec_round_le (impl : RepoImpl) : Prop :=
  ∀ (beta : Radix) (fexp : Int → Int) [ValidExp fexp]
  (rnd : ℝ → Int) [ValidRnd rnd] (x y : ℝ),
  x ≤ y → impl.flocq.round beta fexp rnd x ≤ impl.flocq.round beta fexp rnd y

/-- If y is in generic format and x ≤ y then round(x) ≤ y. -/
def spec_round_le_generic (impl : RepoImpl) : Prop :=
  ∀ (beta : Radix) (fexp : Int → Int) [ValidExp fexp]
  (rnd : ℝ → Int) [ValidRnd rnd] (x y : ℝ),
  genericFormat beta fexp y → x ≤ y →
  impl.flocq.round beta fexp rnd x ≤ y
