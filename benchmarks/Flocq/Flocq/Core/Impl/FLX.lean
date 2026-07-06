-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Flocq.Core.Impl.FLX

FLX (floating-point without underflow) format foundation module, translated
from the Coq source `src/Core/FLX.v`.

`PrecGt0` is a typeclass asserting that a precision parameter `prec` is
strictly positive. `FLX_exp` is the FLX exponent function `e - prec`, used
as the `fexp` argument to the generic floating-point framework throughout
Flocq.

Types and signatures are fixed vocabulary (DO NOT MODIFY). This module has
no computable API functions — it is a pure foundation module imported by
other FLX-related modules.
-/

-- ── Core types (DO NOT MODIFY) ─────────────────────────────────────────────

/-- Typeclass asserting that a precision parameter `prec` is strictly positive.
    This mirrors Coq's `Prec_gt_0` class from `src/Core/FLX.v`. -/
class PrecGt0 (prec : Int) : Prop where
  h : 0 < prec

-- ── Spec helpers (DO NOT MODIFY) ───────────────────────────────────────────

/-- The FLX exponent function: `FLX_exp prec e = e - prec`.
    Used as the `fexp` argument to `generic_format`, `round`, `ulp`, etc.;
    encodes the absence of an underflow bound (no subnormals). -/
def FLX_exp (prec : Int) (e : Int) : Int := e - prec

namespace Flocq

-- ── API signatures (DO NOT MODIFY) ─────────────────────────────────────────
-- (This module exposes only the `PrecGt0` typeclass and `FLX_exp` spec helper;
--  no computable API functions are defined here.)

end Flocq

-- !benchmark @start global_aux
-- !benchmark @end global_aux
