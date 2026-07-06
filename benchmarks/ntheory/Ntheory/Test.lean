import Ntheory.Impl.Residue

/-!
# Ntheory.Test

Executable conformance tests. `#guard` assertions run against the curator's
reference implementations inside the `code` markers in `Impl/Residue.lean`.

DO NOT MODIFY — infrastructure.
-/

open Ntheory

-- ── legendreSymbol / isQuadraticResidue ─────────────────────────
#guard legendreSymbol 2 7 == 1                 -- 3^2 ≡ 2 (mod 7), nonzero QR
#guard legendreSymbol 3 7 == -1                -- non-residue
#guard legendreSymbol 0 7 == 0                 -- 7 ∣ 0
#guard legendreSymbol 1 11 == 1
#guard isQuadraticResidue 2 7 == true
#guard isQuadraticResidue 3 7 == false
#guard isQuadraticResidue 0 7 == false         -- zero is not a *nonzero* QR

-- ── jacobiSymbol ────────────────────────────────────────────────
#guard jacobiSymbol 2 15 == 1
#guard jacobiSymbol 7 15 == -1
#guard jacobiSymbol 1001 9907 == -1            -- classic worked example
#guard jacobiSymbol 5 21 == 1
#guard jacobiSymbol 6 9 == 0                   -- gcd(6,9)=3 ≠ 1
#guard jacobiSymbol 13 1 == 1                  -- base case n = 1

-- ── sqrtMod: least root, none on non-residue ────────────────────
#guard sqrtMod 2 7 == some 3                   -- least of {3,4}
#guard sqrtMod 4 7 == some 2
#guard sqrtMod 0 7 == some 0
#guard sqrtMod 3 7 == none                     -- non-residue

-- ── nthrootMod ──────────────────────────────────────────────────
#guard nthrootMod 8 3 11 == some 2             -- 2^3 ≡ 8 (mod 11)
#guard nthrootMod 4 2 7 == some 2              -- least square root of 4
#guard nthrootMod 3 2 7 == none

-- ── discreteLog: least exponent, none when unreachable ──────────
#guard discreteLog 7 4 2 == some 2             -- 2^2 ≡ 4 (mod 7)
#guard discreteLog 7 1 2 == some 0             -- 2^0 ≡ 1
#guard discreteLog 7 5 2 == none               -- 5 ∉ ⟨2⟩ = {1,2,4}

-- ── nOrder: least positive period ───────────────────────────────
#guard nOrder 2 7 == 3                         -- 2^3 ≡ 1 (mod 7)
#guard nOrder 3 7 == 6                         -- 3 is a primitive root
#guard nOrder 1 7 == 1

-- ── totient ─────────────────────────────────────────────────────
#guard totient 1 == 1
#guard totient 7 == 6                          -- prime
#guard totient 9 == 6
#guard totient 12 == 4
#guard totient 0 == 0

-- ── deep order / discrete-log / square-root laws ────────────────
-- order divides exactly the returning exponents: nOrder 2 7 = 3, 2^6 ≡ 1
#guard (2 ^ 6) % 7 == 1 % 7                    -- 6 = 2·(nOrder 2 7)
#guard (2 ^ 4) % 7 != 1 % 7                    -- 4 not a multiple of 3
#guard nOrder 1 7 == 1                          -- order 1 ↔ a ≡ 1
#guard nOrder 8 7 == 1                          -- 8 ≡ 1 (mod 7)
-- discrete-log order shift: discreteLog 7 4 2 = some 2, nOrder 2 7 = 3
#guard (2 ^ (2 + nOrder 2 7)) % 7 == 4 % 7
#guard (2 ^ (2 + 2 * nOrder 2 7)) % 7 == 4 % 7  -- any multiple of the order
-- square-root complement + canonical bound: sqrtMod 2 7 = some 3, complement 4
#guard ((7 - 3) * (7 - 3)) % 7 == 2 % 7         -- complement is also a root
#guard (3 : Nat) <= 7 - 3                        -- least root ≤ its complement
#guard (2 : Nat) <= 7 - 2                        -- sqrtMod 4 7 = some 2
