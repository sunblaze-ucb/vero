import Flocq.Prop.Impl.Relative

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Flocq.Prop.Impl.MultError

Rounding-error representability for floating-point multiplication,
translated from the Coq source `src/Prop/Mult_error.v`.

This module establishes two key mathematical results:

- **`mult_error_FLX`** (`spec_multErrorFLX`): for any `x`, `y` in FLX
  (floating-point without underflow) format with precision `prec > 0`, the
  rounding error `round_NE(x × y) − (x × y)` is also representable in the
  same FLX format.

- **`mult_error_FLT`** (`spec_multErrorFLT`): for any `x`, `y` in FLT
  (floating-point with gradual underflow) format with minimum exponent `emin`
  and precision `prec > 0`, the rounding error `round_NE(x × y) − (x × y)`
  is also representable in the same FLT format.

The Coq source works with Section variables `beta : radix`, `prec : Z`,
`rnd : R → Z` (a generic valid rounding function), and proves the results
for any `Valid_rnd rnd`. The specs are concretized to `Rounding.NE`
(round-to-nearest, ties resolved downward via `Znearest (fun _ => false)`),
which is imported from `Flocq.Prop.Impl.Relative`.

This is a pure theorem module — it contains no computable API functions.
The key results are captured as `spec_multErrorFLX` and `spec_multErrorFLT`
in the companion Spec file.

Types and signatures are fixed vocabulary (DO NOT MODIFY).
-/

namespace Flocq

-- ── API signatures (DO NOT MODIFY) ───────────────────────────────────────────
-- (This module contains only mathematical theorems; no computable API
--  functions are defined here.)

end Flocq

-- !benchmark @start global_aux
-- !benchmark @end global_aux
