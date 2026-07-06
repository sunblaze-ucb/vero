import Galoistools.Impl.Ring
import Galoistools.Impl.Division

/-!
# Galoistools.Bundle

Per-package implementation bundle for the `Galoistools` root package.
Collects all API signatures into one structure.

DO NOT MODIFY — benchmark infrastructure.
-/

structure GaloistoolsBundle where
  gfAdd     : Galoistools.GfAddSig
  gfSub     : Galoistools.GfSubSig
  gfMul     : Galoistools.GfMulSig
  gfNeg     : Galoistools.GfNegSig
  gfMonic   : Galoistools.GfMonicSig
  gfDiv     : Galoistools.GfDivSig
  gfRem     : Galoistools.GfRemSig
  gfQuo     : Galoistools.GfQuoSig
  gfGcd     : Galoistools.GfGcdSig
  gfGcdex   : Galoistools.GfGcdexSig
  gfPowMod  : Galoistools.GfPowModSig
