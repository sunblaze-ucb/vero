import Ntheory.Impl.Residue

/-!
# Ntheory.Bundle

Per-package implementation bundle for the `Ntheory` root package.
Collects all API signatures into one structure.

DO NOT MODIFY — benchmark infrastructure.
-/

structure NtheoryBundle where
  legendreSymbol      : Ntheory.LegendreSymbolSig
  isQuadraticResidue  : Ntheory.IsQuadraticResidueSig
  jacobiSymbol        : Ntheory.JacobiSymbolSig
  sqrtMod             : Ntheory.SqrtModSig
  nthrootMod          : Ntheory.NthrootModSig
  discreteLog         : Ntheory.DiscreteLogSig
  nOrder              : Ntheory.NOrderSig
  totient             : Ntheory.TotientSig
