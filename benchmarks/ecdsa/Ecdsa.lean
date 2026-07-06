import Ecdsa.Impl.Modular
import Ecdsa.Impl.Curve
import Ecdsa.Bundle
import Ecdsa.Harness
import Ecdsa.Spec.Modular
import Ecdsa.Spec.Curve
import Ecdsa.Test

/-!
# Ecdsa

Root import hub: GF(p) modular arithmetic (`Impl/Modular`, `Spec/Modular`) plus
the elliptic-curve group law in affine coordinates (`Impl/Curve`, `Spec/Curve`).

The headline obligation is `inverseMod`: the modular multiplicative inverse of
`a` mod `m`, characterized by existence-and-uniqueness — the equation
`(a · inv) % m = 1` together with the range clause `0 < inv < m` that pins it to
the unique residue. The curve layer characterizes `containsPoint`, `negPoint`,
`pointDouble`, `pointAdd`, and `scalarMult`; behaviour is pinned by
`Spec/Modular.lean` and `Spec/Curve.lean`.

The benchmark models the curve group law and GF(p) inverse only — not signature
generation/verification. Group associativity is out of scope; the suite covers
the inverse, the on-curve characterization, the coordinate formulas, on-curve
closure (anchored by concrete vectors), and the structural identity / negation /
commutativity / scalar-recurrence laws.
-/
