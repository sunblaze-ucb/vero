import Ecdsa.Impl.Modular
import Ecdsa.Impl.Curve

/-!
# Ecdsa.Bundle

Per-package implementation bundle for the `Ecdsa` root package.
Collects all API signatures into one structure.

DO NOT MODIFY — benchmark infrastructure.
-/

structure EcdsaBundle where
  inverseMod    : Ecdsa.InverseModSig
  isOddPrime    : Ecdsa.IsOddPrimeSig
  jacobi        : Ecdsa.JacobiSig
  sqrtModPrime  : Ecdsa.SqrtModPrimeSig
  containsPoint : Ecdsa.ContainsPointSig
  negPoint      : Ecdsa.NegPointSig
  pointDouble   : Ecdsa.PointDoubleSig
  pointAdd      : Ecdsa.PointAddSig
  scalarMult    : Ecdsa.ScalarMultSig
