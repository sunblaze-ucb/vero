import Flocq.Core.Impl.GenericFmt

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Flocq.Prop.Impl.PlusError

Addition rounding-error representability, translated from the Coq source
`src/Prop/Plus_error.v`.

This module establishes that for any `x`, `y` in a generic floating-point
format, the rounding error `round(x+y) − (x+y)` is itself representable in
the same format, provided the exponent function `fexp` is valid and monotone.

The source file works entirely with the `Znearest choice` rounding function
(ties-to-any-choice round-to-nearest) and uses the section variables
`beta : radix`, `fexp : Z → Z`, `valid_exp : Valid_exp fexp`, and
`monotone_exp : Monotone_exp fexp`.

This is a pure theorem module — it contains no computable API functions.
The key result is captured as `spec_plusError` in the companion Spec file.

Types and signatures are fixed vocabulary (DO NOT MODIFY).
-/

namespace Flocq

-- ── API signatures (DO NOT MODIFY) ───────────────────────────────────────────
-- (This module contains only mathematical theorems; no computable API
--  functions are defined here.)

end Flocq

-- !benchmark @start global_aux
-- !benchmark @end global_aux
