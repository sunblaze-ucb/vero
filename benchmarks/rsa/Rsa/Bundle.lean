import Rsa.Impl.Transform
import Rsa.Impl.Common

/-!
# Rsa.Bundle

Per-package implementation bundle for the `Rsa` root package.
Collects all API signatures into one structure.

DO NOT MODIFY — benchmark infrastructure.
-/

structure RsaBundle where
  encryptInt  : Rsa.EncryptIntSig
  decryptInt  : Rsa.DecryptIntSig
  gcd         : Rsa.GcdSig
  extendedGcd : Rsa.ExtendedGcdSig
  inverse     : Rsa.InverseSig
  crt         : Rsa.CrtSig
