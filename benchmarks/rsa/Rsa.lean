import Rsa.Impl.Transform
import Rsa.Impl.Common
import Rsa.Bundle
import Rsa.Harness
import Rsa.Spec.Transform
import Rsa.Spec.Common
import Rsa.Test

/-!
# Rsa

Root import hub for the RSA number-theory benchmark. The API is the pure
number-theoretic core of RSA over `Nat`/`Int` (mathlib-free, no `Float`):

* `encryptInt m e n` / `decryptInt c d n` — the integer encryption /
  decryption primitives (modular exponentiation `base^exp mod n`).
* `gcd a b`, `extendedGcd a b` — greatest common divisor and its Bézout
  triple `(g, x, y)`.
* `inverse x n` — modular multiplicative inverse.
* `crt residues moduli` — Chinese-Remainder solution.

Behaviour is pinned by the specs in `Spec/Transform.lean` and
`Spec/Common.lean`. The benchmark models the integer-level primitives only:
no key generation, padding, byte/blocksize handling, or ASN.1 encoding.
-/
