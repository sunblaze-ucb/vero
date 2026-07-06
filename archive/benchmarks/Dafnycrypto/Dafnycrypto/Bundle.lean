import Dafnycrypto.Impl.Util.Option
import Dafnycrypto.Impl.Util.Math

/-!
# Dafnycrypto.Bundle

Per-package implementation bundle for the `DafnyCrypto` root package.
Collects all 7 API signatures into one structure.

DO NOT MODIFY — benchmark infrastructure.
-/

structure DafnyCryptoBundle where
  vecMul       : DafnyCrypto.VecMulSig
  vecAdd       : DafnyCrypto.VecAddSig
  pow          : DafnyCrypto.PowSig
  powN         : DafnyCrypto.PowNSig
  modPow       : DafnyCrypto.ModPowSig
  gcdExtended  : DafnyCrypto.GcdExtendedSig
  inverse      : DafnyCrypto.InverseSig
