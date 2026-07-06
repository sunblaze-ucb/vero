import Reedsolo.Impl.Field

/-!
# Reedsolo.Test

Executable conformance tests. `#guard` assertions run against the curator's
reference implementations inside the `code` markers in `Impl/Field.lean`.

DO NOT MODIFY — infrastructure.
-/

open Reedsolo

-- ── gfMul ───────────────────────────────────────────────────────
#guard gfMul 0 5 == 0                  -- 0 annihilates
#guard gfMul 1 200 == 200              -- 1 is the identity
#guard gfMul 3 7 == 9                  -- 0x03 · 0x07 = 0x09
#guard gfMul 2 128 == 29               -- x · x⁷ = x⁸ ≡ 0x1d
#guard gfMul 7 3 == gfMul 3 7          -- commutative

-- ── gfPow ───────────────────────────────────────────────────────
#guard gfPow 2 0 == 1                  -- a⁰ = 1
#guard gfPow 2 4 == 16                 -- α⁴ = 0x10
#guard gfPow 2 8 == 29                 -- α⁸ ≡ 0x1d
#guard gfPow 5 2 == gfMul 5 5          -- a² = a·a

-- ── gfInverse ───────────────────────────────────────────────────
#guard gfInverse 1 == 1                -- 1⁻¹ = 1
#guard gfMul 2 (gfInverse 2) == 1      -- a · a⁻¹ = 1
#guard gfMul 7 (gfInverse 7) == 1      -- a · a⁻¹ = 1

-- ── rsGeneratorPoly ─────────────────────────────────────────────
#guard rsGeneratorPoly 0 == [1]              -- empty product = 1
#guard rsGeneratorPoly 1 == [1, 1]           -- (x + α⁰) = (x + 1)
#guard rsGeneratorPoly 2 == [1, 3, 2]        -- (x+1)(x+α)
#guard rsGeneratorPoly 3 == [1, 7, 14, 8]

-- ── rsEncodeMsg ─────────────────────────────────────────────────
#guard rsEncodeMsg [0x12, 0x34] 2 == [18, 52, 34, 4]          -- systematic prefix [18,52]
#guard rsEncodeMsg [1, 2, 3, 4] 4 == [1, 2, 3, 4, 117, 163, 178, 96]
#guard (rsEncodeMsg [1, 2, 3, 4] 4).take 4 == [1, 2, 3, 4]    -- message preserved
#guard (rsEncodeMsg [1, 2, 3, 4] 4).length == 8              -- length = k + nsym
#guard rsEncodeMsg [] 2 == [0, 0]                             -- empty message
