import Flocq.Prop.Impl.Relative

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Flocq.Prop.Impl.DivSqrtError

Division and square root rounding-error representability for the FLX format,
translated from the Coq source `src/Prop/Div_sqrt_error.v`.

This module establishes that for `x`, `y` in FLX floating-point format, the
rounding errors of division (`round(x/y) − x/y`) and square root
(`round(sqrt x) − sqrt x`) are themselves representable in the same FLX
format. Both results apply to round-to-nearest; the square root result
additionally requires precision `prec > 1`.

The Coq source works within a `Section Fprop_divsqrt_error` parameterized
by `beta : radix`, `prec : Z`, and a choice function `choice : Z → bool`.
Key Coq results translated:
- `div_error_FLX` — division rounding error is in FLX format.
- `sqrt_error_FLX_N` — square root rounding error (nearest) is in FLX format.

This is a pure theorem module — it contains no computable API functions.
The key results are captured as `spec_divErrorFLX` and `spec_sqrtErrorFLXN`
in the companion Spec file.

Arithmetic on ℝ (negation, addition, subtraction, multiplication, division)
and the `ValidExp`, `Rounding.NE`, `genericFormat`, `Flocq.round`, `FLX_exp`
vocabulary are all available transitively through the `Prop.Relative` import
(via `Core.Ulp` → `Core.RoundPred` → `Core.FLT` → `Core.FLX`).

Types and signatures are fixed vocabulary (DO NOT MODIFY).
-/

namespace Flocq

-- ── API signatures (DO NOT MODIFY) ───────────────────────────────────────────
-- (This module contains only mathematical theorems; no computable API
--  functions are defined here.)

end Flocq

-- !benchmark @start global_aux
-- !benchmark @end global_aux
