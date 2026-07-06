import Galoistools.Impl.Ring
import Galoistools.Impl.Division

/-!
# Galoistools.Test

Executable conformance tests. `#guard` assertions run against the curator's
reference implementations in `Impl/Ring.lean` and `Impl/Division.lean`, checked
against SymPy's `sympy.polys.galoistools` (sympy 1.14.0). Polynomials are
big-endian coeff lists over `GF(p)`.

DO NOT MODIFY — infrastructure.
-/

open Galoistools

-- ── gfAdd ────────────────────────────────────────────────────────
#guard gfAdd [3, 2, 4] [2, 2, 2] 5 == [4, 1]
#guard gfAdd [1, 2, 3] [4, 5] 7 == [1, 6, 1]
#guard gfAdd [] [1, 1] 5 == [1, 1]
#guard gfAdd [1, 1] [] 5 == [1, 1]

-- ── gfSub ────────────────────────────────────────────────────────
#guard gfSub [3, 2, 4] [2, 2, 2] 5 == [1, 0, 2]
#guard gfSub [] [1, 2, 3] 5 == [4, 3, 2]      -- = gf_neg
#guard gfSub [1, 2, 3] [1, 2, 3] 5 == []

-- ── gfMul ────────────────────────────────────────────────────────
#guard gfMul [3, 2, 4] [2, 2, 2] 5 == [1, 0, 3, 2, 3]
#guard gfMul [1, 1] [1, 1] 2 == [1, 0, 1]     -- (x+1)^2 = x^2+1 in GF(2)
#guard gfMul [] [1, 2] 5 == []
#guard gfMul [1, 0] [1, 0] 7 == [1, 0, 0]     -- x·x = x^2

-- ── gfNeg ────────────────────────────────────────────────────────
#guard gfNeg [1, 2, 3] 5 == [4, 3, 2]
#guard gfNeg [] 5 == []
#guard gfNeg [0, 4] 5 == [0, 1]

-- ── gfMonic ──────────────────────────────────────────────────────
#guard gfMonic [2, 2, 3] 5 == (2, [1, 1, 4])
#guard gfMonic [3, 2, 4] 5 == (3, [1, 4, 3])
#guard gfMonic [1, 4, 3] 5 == (1, [1, 4, 3])
#guard gfMonic [] 5 == (0, [])

-- ── gfDiv ────────────────────────────────────────────────────────
#guard gfDiv [1, 0, 1, 1] [1, 1, 0] 2 == ([1, 1], [1])
#guard gfDiv [1, 0, 3, 2, 3] [2, 2, 2] 5 == ([3, 2, 4], [])
#guard gfDiv [5, 4, 3, 2, 1] [1, 2, 3] 7 == ([5, 1, 0], [6, 1])
#guard gfDiv [1, 2] [1, 0, 1] 5 == ([], [1, 2])   -- deg f < deg g

-- ── gfRem ────────────────────────────────────────────────────────
#guard gfRem [1, 0, 1, 1] [1, 1, 0] 2 == [1]
#guard gfRem [5, 4, 3, 2, 1] [1, 2, 3] 7 == [6, 1]
#guard gfRem [1, 0, 3, 2, 3] [2, 2, 2] 5 == []

-- ── gfQuo ────────────────────────────────────────────────────────
#guard gfQuo [1, 0, 1, 1] [1, 1, 0] 2 == [1, 1]
#guard gfQuo [1, 0, 3, 2, 3] [2, 2, 2] 5 == [3, 2, 4]
#guard gfQuo [5, 4, 3, 2, 1] [1, 2, 3] 7 == [5, 1, 0]

-- ── gfGcd ────────────────────────────────────────────────────────
#guard gfGcd [3, 2, 4] [2, 2, 3] 5 == [1, 3]
#guard gfGcd [1, 8, 7] [1, 7, 1, 7] 11 == [1, 7]
#guard gfGcd [] [2, 4] 5 == [1, 2]          -- monic of [2,4]
#guard gfGcd [2, 4] [] 5 == [1, 2]
#guard gfGcd [] [] 5 == []

-- ── gfGcdex ──────────────────────────────────────────────────────
#guard gfGcdex [1, 8, 7] [1, 7, 1, 7] 11 == ([5, 6], [6], [1, 7])
#guard gfGcdex [1, 0, 1] [1, 1] 2 == ([], [1], [1, 1])
#guard gfGcdex [3, 2, 4] [2, 2, 3] 5 == ([4], [4], [1, 3])

-- ── gfPowMod ─────────────────────────────────────────────────────
#guard gfPowMod [1, 1] 3 [1, 0, 1] 5 == [2, 3]
#guard gfPowMod [1, 1] 0 [1, 0, 1] 5 == [1]
#guard gfPowMod [1, 1] 1 [1, 0, 1] 5 == [1, 1]
#guard gfPowMod [2, 1] 7 [1, 0, 0, 3] 5 == [3, 1, 3]
