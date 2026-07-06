import Flocq.Harness
import Flocq.Core.Impl.RoundPred

/-!
# Flocq.Core.Spec.RoundPred

Specifications for the rounding predicates defined in `Impl/Core.RoundPred.lean`,
corresponding to key theorems from `src/Core/Round_pred.v`.

The four specs below assert: the DN–UP split property (every F-value lies on
one side of the DN/UP pair), uniqueness of round-down, uniqueness of round-up,
and uniqueness for any monotone rounding relation.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- Every F-valued point lies entirely on one side of the round-down / round-up
    pair: if `d = RndDn(F, x)` and `u = RndUp(F, x)`, then every `f ∈ F`
    satisfies `f ≤ d` or `u ≤ f`.
    Mirrors Coq's `Rnd_DN_UP_pt_split` from `src/Core/Round_pred.v`. -/
def spec_Rnd_DN_UP_pt_split (impl : RepoImpl) : Prop :=
  ∀ (F : ℝ → Prop) (x d u : ℝ),
  RndDnPt F x d → RndUpPt F x u →
  ∀ f : ℝ, F f → f ≤ d ∨ u ≤ f

/-- The round-toward-−∞ point is unique: if `f1` and `f2` are both round-down
    points of `x` in format `F`, then `f1 = f2`.
    Mirrors Coq's `Rnd_DN_pt_unique` from `src/Core/Round_pred.v`. -/
def spec_Rnd_DN_pt_unique (impl : RepoImpl) : Prop :=
  ∀ (F : ℝ → Prop) (x f1 f2 : ℝ),
  RndDnPt F x f1 → RndDnPt F x f2 → f1 = f2

/-- The round-toward-+∞ point is unique: if `f1` and `f2` are both round-up
    points of `x` in format `F`, then `f1 = f2`.
    Mirrors Coq's `Rnd_UP_pt_unique` from `src/Core/Round_pred.v`. -/
def spec_Rnd_UP_pt_unique (impl : RepoImpl) : Prop :=
  ∀ (F : ℝ → Prop) (x f1 f2 : ℝ),
  RndUpPt F x f1 → RndUpPt F x f2 → f1 = f2

/-- A monotone rounding relation maps each `x` to at most one value:
    if `P` is monotone and `P x f1` and `P x f2`, then `f1 = f2`.
    Mirrors Coq's `round_unique` from `src/Core/Round_pred.v`. -/
def spec_round_unique (impl : RepoImpl) : Prop :=
  ∀ (P : ℝ → ℝ → Prop),
  RoundPredMonotone P →
  ∀ (x f1 f2 : ℝ), P x f1 → P x f2 → f1 = f2
