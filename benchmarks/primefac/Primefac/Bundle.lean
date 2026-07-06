import Primefac.Impl.Factor

/-!
# Primefac.Bundle

Per-package implementation bundle for the `Primefac` root package.
Collects all API signatures into one structure.

DO NOT MODIFY — benchmark infrastructure.
-/

structure PrimefacBundle where
  isprime  : Primefac.IsprimeSig
  iterprod : Primefac.IterprodSig
  primefac : Primefac.PrimefacSig
