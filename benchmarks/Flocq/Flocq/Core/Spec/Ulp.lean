import Flocq.Harness
import Flocq.Core.Impl.Ulp

open Flocq

/-!
# Flocq.Core.Spec.Ulp

Specifications for the unit-in-the-last-place, successor, and predecessor
functions defined in `Impl/Core.Ulp.lean`, corresponding to key theorems from
`src/Core/Ulp.v`.

All specs access API functions via `impl.flocq.<fn>` through the `RepoImpl`
harness structure.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- round-up(x) ≤ succ(round-down(x)).
    Mirrors Coq's `round_UP_succ_round_DN` direction. -/
def spec_UP_le_succ_DN (impl : RepoImpl) : Prop :=
  ∀ (beta : Radix) (fexp : Int → Int) [ValidExp fexp] (x : ℝ),
  Flocq.round beta fexp Zceil x ≤ impl.flocq.succ beta fexp (Flocq.round beta fexp Zfloor x)

/-- |round_N(x) - x| ≤ ulp(x)/2.
    Mirrors Coq's `error_le_half_ulp`. -/
def spec_error_le_half_ulp (impl : RepoImpl) : Prop :=
  ∀ (beta : Radix) (fexp : Int → Int) [ValidExp fexp]
  (choice : Int → Bool) (x : ℝ),
  |Flocq.round beta fexp (Znearest choice) x - x| ≤ impl.flocq.ulp beta fexp x / 2

/-- |round_N(x) - x| ≤ ulp(round_N(x))/2.
    Mirrors Coq's `error_le_half_ulp_round`. -/
def spec_error_le_half_ulp_round (impl : RepoImpl) : Prop :=
  ∀ (beta : Radix) (fexp : Int → Int) [ValidExp fexp]
  (choice : Int → Bool) (x : ℝ),
  |Flocq.round beta fexp (Znearest choice) x - x| ≤
    impl.flocq.ulp beta fexp (Flocq.round beta fexp (Znearest choice) x) / 2

/-- For nonzero `x`, |round(x) - x| < ulp(x).
    Mirrors Coq's `error_lt_ulp` (whose `x ≠ 0` hypothesis is required: at
    `x = 0` the error is `0` while `ulp 0 = 0` in formats without a negligible
    exponent, e.g. FLX, so the strict bound fails). -/
def spec_error_lt_ulp (impl : RepoImpl) : Prop :=
  ∀ (beta : Radix) (fexp : Int → Int) [ValidExp fexp]
  (rnd : ℝ → Int) [ValidRnd rnd] (x : ℝ),
  x ≠ 0 →
  |Flocq.round beta fexp rnd x - x| < impl.flocq.ulp beta fexp x

/-- For a monotone exponent function and nonzero `x`, |round(x) - x| < ulp(round(x)).
    Mirrors Coq's `error_lt_ulp_round`, which requires both `Monotone_exp fexp`
    (so the ulp cannot shrink across the rounding step) and `x ≠ 0`. -/
def spec_error_lt_ulp_round (impl : RepoImpl) : Prop :=
  ∀ (beta : Radix) (fexp : Int → Int) [ValidExp fexp] [MonotoneExp fexp]
  (rnd : ℝ → Int) [ValidRnd rnd] (x : ℝ),
  x ≠ 0 →
  |Flocq.round beta fexp rnd x - x| < impl.flocq.ulp beta fexp (Flocq.round beta fexp rnd x)

/-- pred(x) is in generic format whenever x is.
    Mirrors Coq's `generic_format_pred`. -/
def spec_generic_format_pred (impl : RepoImpl) : Prop :=
  ∀ (beta : Radix) (fexp : Int → Int) [ValidExp fexp] (x : ℝ),
  genericFormat beta fexp x → genericFormat beta fexp (impl.flocq.pred beta fexp x)

/-- succ(x) is in generic format whenever x is.
    Mirrors Coq's `generic_format_succ`. -/
def spec_generic_format_succ (impl : RepoImpl) : Prop :=
  ∀ (beta : Radix) (fexp : Int → Int) [ValidExp fexp] (x : ℝ),
  genericFormat beta fexp x → genericFormat beta fexp (impl.flocq.succ beta fexp x)

/-- pred(round-up(x)) ≤ round-down(x).
    Mirrors Coq's `pred_round_UP_le_round_DN`. -/
def spec_pred_UP_le_DN (impl : RepoImpl) : Prop :=
  ∀ (beta : Radix) (fexp : Int → Int) [ValidExp fexp] (x : ℝ),
  impl.flocq.pred beta fexp (Flocq.round beta fexp Zceil x) ≤ Flocq.round beta fexp Zfloor x

/-- pred(x) ≤ x for all formatted x.
    Mirrors Coq's `pred_le_id`. -/
def spec_pred_le_id (impl : RepoImpl) : Prop :=
  ∀ (beta : Radix) (fexp : Int → Int) [ValidExp fexp] (x : ℝ),
  genericFormat beta fexp x → impl.flocq.pred beta fexp x ≤ x

/-- pred(round(x)) ≤ x.
    Mirrors Coq's `pred_round_le`. -/
def spec_pred_round_le_id (impl : RepoImpl) : Prop :=
  ∀ (beta : Radix) (fexp : Int → Int) [ValidExp fexp]
  (rnd : ℝ → Int) [ValidRnd rnd] (x : ℝ),
  impl.flocq.pred beta fexp (Flocq.round beta fexp rnd x) ≤ x

/-- If round-down(x) > 0, round-up(x) ≥ round-down(x).
    Mirrors Coq's `round_DN_ge_0_round_UP_ge`. -/
def spec_round_DN_ge_UP_gt (impl : RepoImpl) : Prop :=
  ∀ (beta : Radix) (fexp : Int → Int) [ValidExp fexp] (x : ℝ),
  0 < Flocq.round beta fexp Zfloor x →
  Flocq.round beta fexp Zfloor x ≤ Flocq.round beta fexp Zceil x

/-- succ(x) ≥ x for all formatted x.
    Mirrors Coq's `succ_ge_id`. -/
def spec_succ_ge_id (impl : RepoImpl) : Prop :=
  ∀ (beta : Radix) (fexp : Int → Int) [ValidExp fexp] (x : ℝ),
  genericFormat beta fexp x → x ≤ impl.flocq.succ beta fexp x

/-- succ(-x) = -pred(x).
    Mirrors Coq's `succ_opp`. -/
def spec_succ_opp (impl : RepoImpl) : Prop :=
  ∀ (beta : Radix) (fexp : Int → Int) [ValidExp fexp] (x : ℝ),
  impl.flocq.succ beta fexp (-x) = -(impl.flocq.pred beta fexp x)

/-- succ(round(x)) ≥ x.
    Mirrors Coq's `succ_round_ge`. -/
def spec_succ_round_ge_id (impl : RepoImpl) : Prop :=
  ∀ (beta : Radix) (fexp : Int → Int) [ValidExp fexp]
  (rnd : ℝ → Int) [ValidRnd rnd] (x : ℝ),
  x ≤ impl.flocq.succ beta fexp (Flocq.round beta fexp rnd x)

/-- ulp(x) ≥ 0.
    Mirrors Coq's `ulp_ge_0`. -/
def spec_ulp_ge_0 (impl : RepoImpl) : Prop :=
  ∀ (beta : Radix) (fexp : Int → Int) [ValidExp fexp] (x : ℝ),
  0 ≤ impl.flocq.ulp beta fexp x

/-- The unit in the last place is invariant under negation. -/
def spec_ulp_opp (impl : RepoImpl) : Prop :=
  ∀ (beta : Radix) (fexp : Int → Int) [ValidExp fexp] (x : ℝ),
  impl.flocq.ulp beta fexp (-x) = impl.flocq.ulp beta fexp x

/-- The unit in the last place is invariant under absolute value. -/
def spec_ulp_abs (impl : RepoImpl) : Prop :=
  ∀ (beta : Radix) (fexp : Int → Int) [ValidExp fexp] (x : ℝ),
  impl.flocq.ulp beta fexp |x| = impl.flocq.ulp beta fexp x

/-- The unit in the last place of a radix power follows the exponent function. -/
def spec_ulp_bpow (impl : RepoImpl) : Prop :=
  ∀ (beta : Radix) (fexp : Int → Int) [ValidExp fexp] (e : Int),
  impl.flocq.ulp beta fexp (Flocq.bpow beta e) = Flocq.bpow beta (fexp (e + 1))

/-- If x is a non-zero formatted float, ulp(x) ≠ 0.
    Mirrors Coq's `ulp_neq_0`. -/
def spec_ulp_neq_0 (impl : RepoImpl) : Prop :=
  ∀ (beta : Radix) (fexp : Int → Int) [ValidExp fexp] (x : ℝ),
  x ≠ 0 → genericFormat beta fexp x → impl.flocq.ulp beta fexp x ≠ 0
