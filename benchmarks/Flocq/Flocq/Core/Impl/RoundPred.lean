import Flocq.Core.Impl.FLT

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Flocq.Core.Impl.RoundPred

Pointwise rounding predicates and the monotone-rounding condition, translated
from the Coq source `src/Core/Round_pred.v`.

This module defines three vocabulary predicates used throughout the Flocq
rounding-mode specifications:

- `RndDnPt F x d` — `d` is the greatest F-value at most `x` (round-toward-−∞).
- `RndUpPt F x u` — `u` is the least F-value at least `x` (round-toward-+∞).
- `RoundPredMonotone P` — the binary relation `P` is monotone (order-preserving).

These correspond directly to `Rnd_DN_pt`, `Rnd_UP_pt`, and `round_pred_monotone`
in `src/Core/Defs.v` / `src/Core/Round_pred.v`.

Types and spec helpers are fixed vocabulary (DO NOT MODIFY). This module has
no computable API functions.
-/

-- ── Spec helpers (DO NOT MODIFY) ─────────────────────────────────────────────

/-- `RndDnPt F x d`: `d` is the round-toward-−∞ of `x` in the float format `F`.
    Concretely: `d ∈ F`, `d ≤ x`, and for every `g ∈ F` with `g ≤ x`, `g ≤ d`
    (i.e., `d` is the greatest F-element not exceeding `x`).
    Mirrors Coq's `Rnd_DN_pt` from `src/Core/Defs.v`. -/
def RndDnPt (F : ℝ → Prop) (x d : ℝ) : Prop :=
  F d ∧ d ≤ x ∧ ∀ g : ℝ, F g → g ≤ x → g ≤ d

/-- `RndUpPt F x u`: `u` is the round-toward-+∞ of `x` in the float format `F`.
    Concretely: `u ∈ F`, `x ≤ u`, and for every `g ∈ F` with `x ≤ g`, `u ≤ g`
    (i.e., `u` is the least F-element not below `x`).
    Mirrors Coq's `Rnd_UP_pt` from `src/Core/Defs.v`. -/
def RndUpPt (F : ℝ → Prop) (x u : ℝ) : Prop :=
  F u ∧ x ≤ u ∧ ∀ g : ℝ, F g → x ≤ g → u ≤ g

/-- `RoundPredMonotone P`: the binary rounding relation `P : ℝ → ℝ → Prop` is
    monotone, i.e., `P x f → P y g → x ≤ y → f ≤ g`.
    Mirrors Coq's `round_pred_monotone` from `src/Core/Defs.v`. -/
def RoundPredMonotone (P : ℝ → ℝ → Prop) : Prop :=
  ∀ (x y f g : ℝ), P x f → P y g → x ≤ y → f ≤ g

namespace Flocq

-- ── API signatures (DO NOT MODIFY) ───────────────────────────────────────────
-- (This module exposes only the three spec-helper predicates above;
--  no computable API functions are defined here.)

end Flocq

-- !benchmark @start global_aux
-- !benchmark @end global_aux
