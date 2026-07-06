import Rsa.Impl.Transform
import Rsa.Impl.Common

/-!
# Rsa.Test

Executable conformance tests. `#guard` assertions run against the curator's
reference implementations inside the `code` markers in `Impl/Transform.lean`
and `Impl/Common.lean`.

DO NOT MODIFY — infrastructure.
-/

open Rsa

-- ── encryptInt: m^e mod n ────────────────────────────────────────
#guard encryptInt 2 10 1000 == 24             -- 1024 mod 1000
#guard encryptInt 7 1 13 == 7                  -- e = 1: just the message
#guard encryptInt 4 13 497 == 445              -- textbook RSA encryption
#guard encryptInt 5 0 7 == 1                   -- e = 0: 5^0 = 1
#guard encryptInt 10 3 1 == 0                  -- n = 1: everything ≡ 0

-- ── decryptInt: c^d mod n ────────────────────────────────────────
#guard decryptInt 445 97 497 == 4              -- inverts the encryption above (d = inverse 13 420)
#guard decryptInt 24 1 1000 == 24              -- d = 1
#guard decryptInt 8 2 5 == 4                   -- 64 mod 5
#guard decryptInt 0 5 7 == 0                   -- 0^5 = 0

-- ── gcd: greatest common divisor ─────────────────────────────────
#guard gcd 240 46 == 2
#guard gcd 17 3120 == 1                        -- coprime
#guard gcd 12 0 == 12                          -- gcd a 0 = a
#guard gcd 0 9 == 9
#guard gcd 36 24 == 12

-- ── extendedGcd: Bézout triple (g, x, y) ─────────────────────────
#guard extendedGcd 240 46 == (2, -9, 47)       -- 240·(-9) + 46·47 = 2
#guard extendedGcd 6 4 == (2, 1, -1)           -- 6·1 + 4·(-1) = 2
#guard extendedGcd 17 3120 == (1, -367, 2)
#guard extendedGcd 5 0 == (5, 1, 0)            -- base case b = 0
#guard extendedGcd 3 11 == (1, 4, -1)

-- ── inverse: modular multiplicative inverse ──────────────────────
#guard inverse 3 11 == 4                        -- 3·4 = 12 ≡ 1 mod 11
#guard inverse 17 3120 == 2753                  -- RSA private exponent
#guard inverse 7 40 == 23                       -- 7·23 = 161 ≡ 1 mod 40
#guard inverse 1 5 == 1                         -- inverse of 1 is 1
#guard (3 * inverse 3 11) % 11 == 1             -- defining property

-- ── crt: Chinese Remainder solution ──────────────────────────────
#guard crt [2, 3] [3, 5] == 8                   -- x ≡ 2 (3), x ≡ 3 (5)
#guard crt [1, 2, 3] [2, 3, 5] == 23            -- three moduli
#guard crt [5] [3] == 2                          -- single modulus: 5 mod 3
#guard (crt [2, 3] [3, 5]) % 3 == 2             -- congruence mod 3
#guard (crt [2, 3] [3, 5]) % 5 == 3             -- congruence mod 5
