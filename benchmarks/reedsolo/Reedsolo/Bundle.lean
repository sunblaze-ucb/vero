import Reedsolo.Impl.Field

/-!
# Reedsolo.Bundle

Per-package implementation bundle for the `Reedsolo` root package.
Collects all API signatures into one structure.

DO NOT MODIFY — benchmark infrastructure.
-/

structure ReedsoloBundle where
  gfMul           : Reedsolo.GfMulSig
  gfPow           : Reedsolo.GfPowSig
  gfInverse       : Reedsolo.GfInverseSig
  rsGeneratorPoly : Reedsolo.RsGeneratorPolySig
  rsEncodeMsg     : Reedsolo.RsEncodeMsgSig
