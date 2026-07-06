import Dafnycrypto.Impl.Util.Option
import Dafnycrypto.Impl.Util.Math

/-!
# Dafnycrypto.Test

Executable conformance tests. `#guard` assertions run against the
curator's reference implementations that live INSIDE the `code`
markers in `Impl/*.lean`. Before the LLM sees the benchmark, the
pipeline replaces marker contents with `sorry` — these guards catch
regressions in the reference impls themselves, not in LLM submissions.

DO NOT MODIFY — infrastructure.
-/

open DafnyCrypto

-- ── vecMul / vecAdd ─────────────────────────────────────────────────────────
#guard vecMul [1, 2, 3] [4, 5, 6] == [4, 10, 18]
#guard vecAdd [1, 2, 3] [4, 5, 6] == [5, 7, 9]
#guard vecMul ([] : List Int) [] == []
#guard vecAdd [0] [0] == [0]

-- ── pow ─────────────────────────────────────────────────────────────────────
#guard pow 2 0 == 1
#guard pow 2 10 == 1024
#guard pow 3 3 == 27
#guard pow 0 0 == 1

-- ── powN ────────────────────────────────────────────────────────────────────
#guard powN 2 0 == []
#guard powN 2 4 == [1, 2, 4, 8]
#guard powN 3 3 == [1, 3, 9]

-- ── modPow ──────────────────────────────────────────────────────────────────
#guard modPow 3 4 7 == 4      -- 81 % 7 = 4
#guard modPow 2 10 1000 == 24 -- 1024 % 1000 = 24
#guard modPow 5 0 7 == 1      -- 1 % 7 = 1

-- ── gcdExtended ─────────────────────────────────────────────────────────────
#guard (gcdExtended 3 7).1 == 1    -- gcd(3,7) = 1
#guard (gcdExtended 0 5).1 == 5    -- gcd(0,5) = 5
#guard (let (g, x, y) := gcdExtended 3 7; 3 * x + 7 * y == g)  -- Bezout identity

-- ── inverse ─────────────────────────────────────────────────────────────────
#guard inverse 3 7 == some 5   -- 3 * 5 = 15 ≡ 1 (mod 7)
#guard inverse 1 7 == some 1   -- 1 * 1 = 1 ≡ 1 (mod 7)
#guard inverse 2 4 == none     -- gcd(2,4) = 2 > 1, no inverse
