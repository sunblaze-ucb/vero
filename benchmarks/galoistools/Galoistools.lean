import Galoistools.Impl.Ring
import Galoistools.Impl.Division
import Galoistools.Bundle
import Galoistools.Harness
import Galoistools.Spec.Ring
import Galoistools.Spec.Division
import Galoistools.Test

/-!
# Galoistools

Root import hub: univariate polynomials over the prime field `GF(p)`, ported
from SymPy's `sympy/polys/galoistools.py`. Polynomials are big-endian
coefficient lists over `GF(p)` (head = leading coeff, `[]` = zero polynomial).

Ring layer (`Impl/Ring`, `Spec/Ring`): `gfAdd`, `gfSub`, `gfMul`, `gfNeg`,
`gfMonic`.

Division layer (`Impl/Division`, `Spec/Division`): the headline `gfDiv`
(Euclidean division `f = q·g + r`, `deg r < deg g`, with `(q, r)` the unique
such pair), its projections `gfRem` / `gfQuo`, the monic `gfGcd`, extended
Euclid `gfGcdex` (`s·f + t·g = gcd`), and `gfPowMod` (`f^n mod g`).

Behaviour is pinned by `Spec/Ring.lean` and `Spec/Division.lean`.
-/
