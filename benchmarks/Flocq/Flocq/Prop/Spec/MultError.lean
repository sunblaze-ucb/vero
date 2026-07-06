import Flocq.Harness
import Flocq.Prop.Impl.MultError

open Flocq

/-!
# Flocq.Prop.Spec.MultError

Specifications for multiplication rounding-error representability,
translated from the Coq source `src/Prop/Mult_error.v`.

Both specs assert that for `x`, `y` in a floating-point format, the rounding
error `round_NE(x × y) − (x × y)` is itself representable in the same
floating-point format. The two variants cover:

- **FLX** (no underflow): the result holds unconditionally whenever both
  operands are in FLX format.
- **FLT** (gradual underflow / subnormals): the result holds whenever both
  operands are in FLT format.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- The rounding error of FLX multiplication is representable:
    for any `x`, `y` in `FLX_exp prec` format with `0 < prec`, the error
    `round_NE(x × y) − (x × y)` is also in `FLX_exp prec` format.
    Corresponds to Coq `mult_error_FLX` from `src/Prop/Mult_error.v`. -/
def spec_multErrorFLX (impl : RepoImpl) : Prop :=
  ∀ (beta : Radix) (prec : Int),
  0 < prec →
  ∀ (x y : ℝ),
  genericFormat beta (FLX_exp prec) x →
  genericFormat beta (FLX_exp prec) y →
  genericFormat beta (FLX_exp prec)
    (round beta (FLX_exp prec) Rounding.NE (x * y) - (x * y))

/-- The rounding error of FLT multiplication is representable:
    for any `x`, `y` in `FLT_exp emin prec` format with `0 < prec`, the error
    `round_NE(x × y) − (x × y)` is also in `FLT_exp emin prec` format.
    Corresponds to Coq `mult_error_FLT` from `src/Prop/Mult_error.v`. -/
def spec_multErrorFLT (impl : RepoImpl) : Prop :=
  ∀ (beta : Radix) (emin prec : Int),
  0 < prec →
  ∀ (x y : ℝ),
  genericFormat beta (FLT_exp emin prec) x →
  genericFormat beta (FLT_exp emin prec) y →
  genericFormat beta (FLT_exp emin prec)
    (round beta (FLT_exp emin prec) Rounding.NE (x * y) - (x * y))
