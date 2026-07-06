import Flocq.Core.Impl.RoundPred

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Flocq.Core.Impl.Ulp

Unit-in-the-last-place, successor, and predecessor for generic floating-point
formats, translated from the Coq source `src/Core/Ulp.v`.

`ulp beta fexp x` is already defined in `Flocq.Core.Impl.FLT` (imported
transitively) as `bpow beta (cexp beta fexp x)`.  This module contributes the
missing arithmetic infrastructure (negation, addition, subtraction, division on
ℝ), the `ValidExp` typeclass, the three rounding-direction functions
(`Zfloor`, `Zceil`, `Znearest`), and the two successor/predecessor APIs.

- `succ beta fexp x` — next representable float above x: `x + ulp(x)` for
  x ≥ 0, `-predPos(-x)` for x < 0.
- `pred beta fexp x` — previous representable float: `-succ(-x)`.

Types, axioms, and signatures are fixed vocabulary (DO NOT MODIFY).
Implement only the function bodies inside `!benchmark code` markers.
-/

-- ── Spec helpers (DO NOT MODIFY) ─────────────────────────────────────────────

-- ── API signatures (DO NOT MODIFY) ─────────────────────────────────────────

namespace Flocq

-- Note: `UlpSig` and `Flocq.ulp` are already defined in `Flocq.Core.Impl.FLT`
-- (imported transitively).  They are re-used without redefinition.

/-- Signature for `succ`: next representable float above the input. -/
abbrev SuccSig := Radix → (Int → Int) → ℝ → ℝ

/-- Signature for `pred`: previous representable float below the input. -/
abbrev PredSig := Radix → (Int → Int) → ℝ → ℝ

end Flocq

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- ── pred_pos helper ──────────────────────────────────────────────────────────

/-- `predPos beta fexp x`: predecessor of a positive formatted value `x`.

    When `x` equals `bpow beta (mag beta x − 1)` (exact power-of-beta boundary),
    the predecessor falls into the lower binade:
      `x − bpow beta (fexp (mag beta x − 1))`.
    Otherwise it is simply `x − ulp x`.

    Private to this module; mirrors Coq's `pred_pos` from `src/Core/Ulp.v`. -/
private noncomputable def predPos (beta : Radix) (fexp : Int → Int) (x : ℝ) : ℝ :=
  if x = Flocq.bpow beta (Flocq.mag beta x - 1) then
    x - Flocq.bpow beta (fexp (Flocq.mag beta x - 1))
  else
    x - Flocq.ulp beta fexp x

-- ── succ ─────────────────────────────────────────────────────────────────────


/-- `succ beta fexp x`: the least representable float strictly greater than `x`.

    For `x ≥ 0`: `x + ulp(x)`.
    For `x < 0`: `-predPos(-x)` (negate the predecessor of `-x`).

    Mirrors Coq's `succ` from `src/Core/Ulp.v`. -/
noncomputable def Flocq.succ : Flocq.SuccSig :=
  fun beta fexp x =>
    if 0 ≤ x then
      x + Flocq.ulp beta fexp x
    else
      -(predPos beta fexp (-x))

-- ── pred ─────────────────────────────────────────────────────────────────────


/-- `pred beta fexp x`: the greatest representable float strictly less than `x`.

    Defined as `-succ(-x)`.

    Mirrors Coq's `pred` from `src/Core/Ulp.v`. -/
noncomputable def Flocq.pred : Flocq.PredSig :=
  fun beta fexp x => -(Flocq.succ beta fexp (-x))
