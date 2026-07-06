import NumberTheory.Impl.GreatestCommonDivisor
import NumberTheory.Impl.GcdOfNNumbers
import NumberTheory.Impl.LeastCommonMultiple
import NumberTheory.Impl.ExtendedEuclideanAlgorithm
import NumberTheory.Impl.ChineseRemainderTheorem
import NumberTheory.Harness

/-!
# NumberTheory.Test

Executable conformance tests. `#guard` assertions run against the
`canonical` wiring. Before the LLM sees the benchmark, the pipeline
replaces `sorry` stubs — these guards catch regressions in the
reference impls themselves.

DO NOT MODIFY — infrastructure.
-/

-- ── greatest_common_divisor ─────────────────────────────────────────
#guard canonical.numberTheory.greatest_common_divisor 24 40 == 8
#guard canonical.numberTheory.greatest_common_divisor 1 1 == 1
#guard canonical.numberTheory.greatest_common_divisor 1 800 == 1
#guard canonical.numberTheory.greatest_common_divisor 11 37 == 1
#guard canonical.numberTheory.greatest_common_divisor 16 4 == 4
#guard canonical.numberTheory.greatest_common_divisor (-3) 9 == 3
#guard canonical.numberTheory.greatest_common_divisor 9 (-3) == 3
#guard canonical.numberTheory.greatest_common_divisor 3 (-9) == 3
#guard canonical.numberTheory.greatest_common_divisor (-3) (-9) == 3
#guard canonical.numberTheory.greatest_common_divisor 0 0 == 0
#guard canonical.numberTheory.greatest_common_divisor 0 5 == 5
#guard canonical.numberTheory.greatest_common_divisor 5 0 == 5
#guard canonical.numberTheory.greatest_common_divisor 48 18 == 6
#guard canonical.numberTheory.greatest_common_divisor 100 75 == 25

-- ── gcd_by_iterative ────────────────────────────────────────────────
#guard canonical.numberTheory.gcd_by_iterative 24 40 == 8
#guard canonical.numberTheory.gcd_by_iterative (-3) (-9) == 3
#guard canonical.numberTheory.gcd_by_iterative 3 (-9) == 3
#guard canonical.numberTheory.gcd_by_iterative 1 (-800) == 1
#guard canonical.numberTheory.gcd_by_iterative 11 37 == 1
#guard canonical.numberTheory.gcd_by_iterative 0 0 == 0
#guard canonical.numberTheory.gcd_by_iterative 0 5 == 5
#guard canonical.numberTheory.gcd_by_iterative 5 0 == 5
#guard canonical.numberTheory.gcd_by_iterative 48 18 == 6
#guard canonical.numberTheory.gcd_by_iterative 100 75 == 25

-- ── get_factors ────────────────────────────────────────────────────
#guard canonical.numberTheory.get_factors 45 [] 2 == [(3, 2), (5, 1)]
#guard canonical.numberTheory.get_factors 2520 [] 2 == [(2, 3), (3, 2), (5, 1), (7, 1)]
#guard canonical.numberTheory.get_factors 23 [] 2 == [(23, 1)]
#guard canonical.numberTheory.get_factors 12 [] 2 == [(2, 2), (3, 1)]
#guard canonical.numberTheory.get_factors 100 [] 2 == [(2, 2), (5, 2)]

-- ── get_greatest_common_divisor ────────────────────────────────────
#guard canonical.numberTheory.get_greatest_common_divisor [18, 45] == 9
#guard canonical.numberTheory.get_greatest_common_divisor [23, 37] == 1
#guard canonical.numberTheory.get_greatest_common_divisor [2520, 8350] == 10
#guard canonical.numberTheory.get_greatest_common_divisor [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] == 1
#guard canonical.numberTheory.get_greatest_common_divisor [12, 18, 24] == 6

-- ── least_common_multiple_slow ─────────────────────────────────────
#guard canonical.numberTheory.least_common_multiple_slow 5 2 == 10
#guard canonical.numberTheory.least_common_multiple_slow 12 76 == 228
#guard canonical.numberTheory.least_common_multiple_slow 10 20 == 20
#guard canonical.numberTheory.least_common_multiple_slow 13 15 == 195
#guard canonical.numberTheory.least_common_multiple_slow 4 31 == 124
#guard canonical.numberTheory.least_common_multiple_slow 10 42 == 210
#guard canonical.numberTheory.least_common_multiple_slow 43 34 == 1462
#guard canonical.numberTheory.least_common_multiple_slow 5 12 == 60
#guard canonical.numberTheory.least_common_multiple_slow 12 25 == 300
#guard canonical.numberTheory.least_common_multiple_slow 10 25 == 50
#guard canonical.numberTheory.least_common_multiple_slow 6 9 == 18
#guard canonical.numberTheory.least_common_multiple_slow 1 1 == 1
#guard canonical.numberTheory.least_common_multiple_slow 1 100 == 100
#guard canonical.numberTheory.least_common_multiple_slow 100 1 == 100

-- ── least_common_multiple_fast ─────────────────────────────────────
#guard canonical.numberTheory.least_common_multiple_fast 5 2 == 10
#guard canonical.numberTheory.least_common_multiple_fast 12 76 == 228
#guard canonical.numberTheory.least_common_multiple_fast 10 20 == 20
#guard canonical.numberTheory.least_common_multiple_fast 13 15 == 195
#guard canonical.numberTheory.least_common_multiple_fast 4 31 == 124
#guard canonical.numberTheory.least_common_multiple_fast 10 42 == 210
#guard canonical.numberTheory.least_common_multiple_fast 43 34 == 1462
#guard canonical.numberTheory.least_common_multiple_fast 5 12 == 60
#guard canonical.numberTheory.least_common_multiple_fast 12 25 == 300
#guard canonical.numberTheory.least_common_multiple_fast 10 25 == 50
#guard canonical.numberTheory.least_common_multiple_fast 6 9 == 18
#guard canonical.numberTheory.least_common_multiple_fast 0 10 == 0
#guard canonical.numberTheory.least_common_multiple_fast 10 0 == 0
#guard canonical.numberTheory.least_common_multiple_fast 1 1 == 1
#guard canonical.numberTheory.least_common_multiple_fast 1 100 == 100
#guard canonical.numberTheory.least_common_multiple_fast 100 1 == 100

-- ── extended_euclidean_algorithm ───────────────────────────────────
#guard canonical.numberTheory.extended_euclidean_algorithm 1 24 == (1, 0)
#guard canonical.numberTheory.extended_euclidean_algorithm 8 14 == (2, -1)
#guard canonical.numberTheory.extended_euclidean_algorithm 240 46 == (-9, 47)
#guard canonical.numberTheory.extended_euclidean_algorithm 1 (-4) == (1, 0)
#guard canonical.numberTheory.extended_euclidean_algorithm (-2) (-4) == (-1, 0)
#guard canonical.numberTheory.extended_euclidean_algorithm 0 (-4) == (0, -1)
#guard canonical.numberTheory.extended_euclidean_algorithm 2 0 == (1, 0)
#guard canonical.numberTheory.extended_euclidean_algorithm 123456789 987654321 == (-8, 1)
#guard canonical.numberTheory.extended_euclidean_algorithm (-123) (-456) == (63, -17)

-- ── extended_euclid ────────────────────────────────────────────────
#guard canonical.numberTheory.extended_euclid 10 6 == (-1, 2)
#guard canonical.numberTheory.extended_euclid 7 5 == (-2, 3)
#guard canonical.numberTheory.extended_euclid 15 4 == (-1, 4)
#guard canonical.numberTheory.extended_euclid 0 5 == (0, 1)
#guard canonical.numberTheory.extended_euclid 5 0 == (1, 0)

-- ── chinese_remainder_theorem ──────────────────────────────────────
#guard canonical.numberTheory.chinese_remainder_theorem 5 1 7 3 == 31
#guard canonical.numberTheory.chinese_remainder_theorem 6 1 4 3 == 14
#guard canonical.numberTheory.chinese_remainder_theorem 3 2 5 3 == 8
#guard canonical.numberTheory.chinese_remainder_theorem 5 0 7 0 == 0

-- ── invert_modulo ──────────────────────────────────────────────────
#guard canonical.numberTheory.invert_modulo 3 11 == 4
#guard canonical.numberTheory.invert_modulo 10 17 == 12
#guard canonical.numberTheory.invert_modulo 7 13 == 2
#guard canonical.numberTheory.invert_modulo 0 5 == 0

-- ── chinese_remainder_theorem2 ─────────────────────────────────────
#guard canonical.numberTheory.chinese_remainder_theorem2 5 1 7 3 == 31
#guard canonical.numberTheory.chinese_remainder_theorem2 6 1 4 3 == 14
#guard canonical.numberTheory.chinese_remainder_theorem2 3 2 5 3 == 8
#guard canonical.numberTheory.chinese_remainder_theorem2 5 0 7 0 == 0
