import Primepy.Bundle

/-!
# Primepy.Harness

Benchmark harness: `RepoImpl` structure (one field per package),
`canonical` instance wiring.

DO NOT MODIFY — this is benchmark infrastructure.
-/

structure RepoImpl where
  primepy : PrimepyBundle

def canonical : RepoImpl where
  primepy := {
    factor := Primepy.factor
    check := Primepy.check
    factors := Primepy.factors
    phi := Primepy.phi
    first := Primepy.first
    upto := Primepy.upto
    between := Primepy.between
  }
