import Flocq.Core.Impl.Ulp

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Flocq.Prop.Impl.Relative

Relative error vocabulary for generic floating-point rounding, translated from
the Coq source `src/Prop/Relative.v`.

This module provides:
- A `Max ℝ` instance (needed for the FLT combined error bound).
- The `Rounding` namespace with two concrete rounding-direction constants:
  `DN` (round-toward-negative-infinity, i.e. `Zfloor`) and
  `NE` (round-to-nearest with a fixed tie-breaking rule, i.e. `Znearest (fun _ => false)`).

Types and spec helpers are fixed vocabulary (DO NOT MODIFY). This module has
no computable API functions — it is a pure theory module.
-/

-- ── Spec helpers (DO NOT MODIFY) ─────────────────────────────────────────────

/-- Maximum of two real numbers; used in the FLT combined error bound. -/
noncomputable instance : Max ℝ where
  max x y := if x ≤ y then y else x

-- ── Concrete rounding directions as functions ℝ → Int (DO NOT MODIFY) ─────────

namespace Rounding

/-- Round-toward-negative-infinity: `DN x = ⌊x⌋`.
    Mirrors Coq's `Zfloor` used as `rnd` in `round beta fexp Zfloor x`. -/
noncomputable def DN : ℝ → Int := Zfloor

/-- Round-to-nearest (ties resolved downward): `Znearest (fun _ => false)`.
    The error bound `|round_NE x − x| ≤ ulp(x)/2` holds for every
    tie-breaking choice; this picks one concrete representative. -/
noncomputable def NE : ℝ → Int := Znearest (fun _ => false)

end Rounding

namespace Flocq

-- ── API signatures (DO NOT MODIFY) ───────────────────────────────────────────
-- (This module has no computable API functions — it exposes only the
--  Rounding vocabulary above.)

end Flocq

-- !benchmark @start global_aux
-- !benchmark @end global_aux
