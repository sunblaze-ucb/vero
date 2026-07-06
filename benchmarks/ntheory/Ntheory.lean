import Ntheory.Impl.Residue
import Ntheory.Bundle
import Ntheory.Harness
import Ntheory.Spec.Residue
import Ntheory.Test

/-!
# Ntheory

Root import hub for the residue-number-theory benchmark: quadratic-residue /
Legendre / Jacobi symbols, the modular square and nth roots, the discrete
logarithm, the multiplicative order, and Euler's totient. Every value is
discrete — `Nat` residues, `Int` symbol values in `{-1, 0, 1}`; no `Float`.

Legendre/Jacobi symbols are meaningful at odd prime / odd `n`; the
existential and minimality clauses range over residues `x < p`. `nOrder`
returns `0` as the "no order found" sentinel and `totient 0 = 0`.
Behaviour is pinned by the specs in `Spec/Residue.lean`.
-/
