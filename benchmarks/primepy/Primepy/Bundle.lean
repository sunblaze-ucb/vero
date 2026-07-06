import Primepy.Impl.Primes

/-!
# Primepy.Bundle

Per-package implementation bundle. Collects all API signatures into
one `structure PrimepyBundle`.

DO NOT MODIFY — benchmark infrastructure.
-/

structure PrimepyBundle where
  factor : Primepy.FactorSig
  check : Primepy.CheckSig
  factors : Primepy.FactorsSig
  phi : Primepy.PhiSig
  first : Primepy.FirstSig
  upto : Primepy.UptoSig
  between : Primepy.BetweenSig
