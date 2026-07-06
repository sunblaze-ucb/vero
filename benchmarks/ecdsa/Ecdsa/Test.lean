import Ecdsa.Impl.Modular
import Ecdsa.Impl.Curve

/-!
# Ecdsa.Test

Executable conformance tests. `#guard` assertions run against the curator's
reference implementations inside the `code` markers in `Impl/Modular.lean` and
`Impl/Curve.lean`.

DO NOT MODIFY — infrastructure.
-/

open Ecdsa

-- ── inverseMod ──────────────────────────────────────────────────
#guard inverseMod 3 11 == 4        -- 3*4 = 12 ≡ 1 (mod 11)
#guard inverseMod 10 17 == 12      -- 10*12 = 120 ≡ 1 (mod 17)
#guard inverseMod 7 13 == 2        -- 7*2 = 14 ≡ 1 (mod 13)
#guard inverseMod 1 5 == 1         -- inverse of 1 is 1
#guard (3 * inverseMod 3 11) % 11 == 1
#guard (10 * inverseMod 10 17) % 17 == 1

-- ── isOddPrime ──────────────────────────────────────────────────
#guard isOddPrime 7 == true
#guard isOddPrime 17 == true
#guard isOddPrime 9 == false       -- 3 ∣ 9
#guard isOddPrime 2 == false       -- even
#guard isOddPrime 1 == false

-- ── jacobi ──────────────────────────────────────────────────────
#guard jacobi 2 7 == 1             -- 3² = 9 ≡ 2 (mod 7), residue
#guard jacobi 3 7 == -1            -- non-residue
#guard jacobi 2 17 == 1            -- 6² = 36 ≡ 2 (mod 17)
#guard jacobi 0 7 == 0

-- ── sqrtModPrime ────────────────────────────────────────────────
#guard (let r := sqrtModPrime 2 7;  (r * r) % 7 == 2 % 7)
#guard (let r := sqrtModPrime 2 17; (r * r) % 17 == 2 % 17)
#guard (let r := sqrtModPrime 9 17; (r * r) % 17 == 9 % 17)
#guard sqrtModPrime 2 7 < 7

-- ── containsPoint ───────────────────────────────────────────────
-- curve y² = x³ + 2x + 2 (mod 17), generator (5, 1)
#guard containsPoint { p := 17, a := 2, b := 2 } (.affine 5 1) == true
#guard containsPoint { p := 17, a := 2, b := 2 } (.affine 6 3) == true
#guard containsPoint { p := 17, a := 2, b := 2 } (.affine 5 2) == false
#guard containsPoint { p := 17, a := 2, b := 2 } .infinity == true

-- ── negPoint ────────────────────────────────────────────────────
#guard negPoint { p := 17, a := 2, b := 2 } (.affine 5 1) == .affine 5 16
#guard negPoint { p := 17, a := 2, b := 2 } .infinity == .infinity
#guard negPoint { p := 17, a := 2, b := 2 } (.affine 6 3) == .affine 6 14

-- ── pointDouble ─────────────────────────────────────────────────
#guard pointDouble { p := 17, a := 2, b := 2 } (.affine 5 1) == .affine 6 3   -- 2G
#guard pointDouble { p := 17, a := 2, b := 2 } (.affine 6 3) == .affine 3 1   -- 4G
#guard pointDouble { p := 17, a := 2, b := 2 } .infinity == .infinity

-- ── pointAdd ────────────────────────────────────────────────────
#guard pointAdd { p := 17, a := 2, b := 2 } (.affine 5 1) (.affine 6 3) == .affine 10 6  -- 3G
#guard pointAdd { p := 17, a := 2, b := 2 } (.affine 5 1) (.affine 5 16) == .infinity    -- G + (-G)
#guard pointAdd { p := 17, a := 2, b := 2 } .infinity (.affine 5 1) == .affine 5 1       -- O + G
#guard pointAdd { p := 17, a := 2, b := 2 } (.affine 5 1) (.affine 5 1) ==
       pointDouble { p := 17, a := 2, b := 2 } (.affine 5 1)                             -- P + P = 2P

-- ── scalarMult ──────────────────────────────────────────────────
#guard scalarMult { p := 17, a := 2, b := 2 } 0 (.affine 5 1) == .infinity
#guard scalarMult { p := 17, a := 2, b := 2 } 1 (.affine 5 1) == .affine 5 1
#guard scalarMult { p := 17, a := 2, b := 2 } 2 (.affine 5 1) == .affine 6 3
#guard scalarMult { p := 17, a := 2, b := 2 } 3 (.affine 5 1) == .affine 10 6
