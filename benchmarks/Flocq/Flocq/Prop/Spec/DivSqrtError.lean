import Flocq.Harness
import Flocq.Prop.Impl.DivSqrtError

open Flocq

/-!
# Flocq.Prop.Spec.DivSqrtError

Specifications for FLX division and square root rounding-error representability,
translated from the Coq source `src/Prop/Div_sqrt_error.v`.

Both specs assert that the rounding error of an FLX operation is itself
representable in the same FLX format:
- `spec_divErrorFLX` — the error `round(x/y) − x/y` is in FLX format.
- `spec_sqrtErrorFLXN` — the error `round(sqrt x) − sqrt x` is in FLX format
  (nearest rounding, with `prec > 1`).

These are purely mathematical properties of the axiomatized `genericFormat`
and `round` functions. The `impl` parameter is present for uniformity but
unused in the body, as this module has no computable API functions.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- FLX division rounding error is representable in FLX format:
    for any `x`, `y` in FLX format with precision `prec > 0` and `y ≠ 0`,
    the rounding error `round(x/y) − x/y` (under round-to-nearest) is also
    representable in FLX format.
    Corresponds to Coq `div_error_FLX` from `src/Prop/Div_sqrt_error.v`. -/
def spec_divErrorFLX (impl : RepoImpl) : Prop :=
  ∀ (beta : Radix) (prec : Int) (_ : 0 < prec) (_ : 1 < beta.val)
    (x y : ℝ) (_ : genericFormat beta (FLX_exp prec) x)
    (_ : genericFormat beta (FLX_exp prec) y) (_ : y ≠ 0),
    genericFormat beta (FLX_exp prec)
      (round beta (FLX_exp prec) Rounding.NE (x / y) - (x / y))

/-- FLX square root rounding error (nearest) is representable in FLX format:
    for any `x ≥ 0` in FLX format with precision `prec > 1`, the rounding
    error `round(sqrt x) − sqrt x` (under round-to-nearest) is representable
    in FLX format.
    Corresponds to Coq `sqrt_error_FLX_N` from `src/Prop/Div_sqrt_error.v`. -/
def spec_sqrtErrorFLXN (impl : RepoImpl) : Prop :=
  ∀ (beta : Radix) (prec : Int) (_ : 1 < prec)
    (x : ℝ) (_ : genericFormat beta (FLX_exp prec) x) (_ : 0 ≤ x),
    genericFormat beta (FLX_exp prec)
      (round beta (FLX_exp prec) Rounding.NE (Real.sqrt x) - Real.sqrt x)
