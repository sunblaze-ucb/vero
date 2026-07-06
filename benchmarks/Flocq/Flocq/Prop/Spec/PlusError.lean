import Flocq.Harness
import Flocq.Prop.Impl.PlusError

/-!
# Flocq.Prop.Spec.PlusError

Specification for addition rounding-error representability, translated from
the Coq source `src/Prop/Plus_error.v`.

The central theorem (`plus_error` in Coq) states that for any `x`, `y` in
a generic floating-point format with a valid monotone exponent function
`fexp`, and for any tie-breaking function `choice`, the rounding error
`round_NE(x+y) − (x+y)` is also representable in the same format.

The spec universally quantifies over `choice : Int → Bool` because the Coq
source works with an arbitrary section variable `choice : Z → bool`; the
result holds for every nearest-rounding tie-breaking function, not merely
the ties-to-even variant.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- The rounding error of floating-point addition is representable:
    for any `x`, `y` in generic format with a valid monotone exponent function
    `fexp`, and for any nearest-rounding tie-breaking function `choice`, the
    error `round(x+y) − (x+y)` is itself in the same generic format.
    Corresponds to Coq `plus_error` from `src/Prop/Plus_error.v`. -/
def spec_plusError (impl : RepoImpl) : Prop :=
  ∀ (beta : Radix) (fexp : Int → Int) [ValidExp fexp] [MonotoneExp fexp]
    (choice : Int → Bool) (x y : ℝ),
    genericFormat beta fexp x → genericFormat beta fexp y →
    genericFormat beta fexp
      (impl.flocq.round beta fexp (Znearest choice) (x + y) - (x + y))
