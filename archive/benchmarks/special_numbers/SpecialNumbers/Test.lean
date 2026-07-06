import SpecialNumbers.Impl.GreatestCommonDivisor
import SpecialNumbers.Impl.ArmstrongNumbers
import SpecialNumbers.Impl.AutomorphicNumber
import SpecialNumbers.Impl.BellNumbers
import SpecialNumbers.Impl.CarmichaelNumber
import SpecialNumbers.Impl.CatalanNumber
import SpecialNumbers.Impl.HammingNumbers
import SpecialNumbers.Impl.HappyNumber
import SpecialNumbers.Impl.HarshadNumbers
import SpecialNumbers.Impl.HexagonalNumber
import SpecialNumbers.Impl.KrishnamurthyNumber
import SpecialNumbers.Impl.PerfectNumber
import SpecialNumbers.Impl.PolygonalNumbers
import SpecialNumbers.Impl.PronicNumber
import SpecialNumbers.Impl.ProthNumber
import SpecialNumbers.Impl.TriangularNumbers
import SpecialNumbers.Impl.UglyNumbers
import SpecialNumbers.Impl.WeirdNumber
import SpecialNumbers.Bundle
import SpecialNumbers.Harness

/-!
# SpecialNumbers.Test

`#guard` conformance tests for every public API. Each guard goes through
`canonical.specialNumbers.<api>` so the tests exercise the `RepoImpl`
wiring as well as the reference implementations. Pre-agent-gen replaces
the `code` markers with `sorry`; these guards catch regressions in the
reference impls during curation.

DO NOT MODIFY — infrastructure.
-/

-- ── GreatestCommonDivisor ──────────────────────────────────────────────────

#guard canonical.specialNumbers.greatest_common_divisor 24 40 == 8
#guard canonical.specialNumbers.greatest_common_divisor 1 1 == 1
#guard canonical.specialNumbers.greatest_common_divisor (-3) 9 == 3
#guard canonical.specialNumbers.greatest_common_divisor 3 (-9) == 3
#guard canonical.specialNumbers.greatest_common_divisor 0 5 == 5
#guard canonical.specialNumbers.greatest_common_divisor 17 5 == 1

#guard canonical.specialNumbers.gcd_by_iterative 24 40 == 8
#guard canonical.specialNumbers.gcd_by_iterative 1 1 == 1
#guard canonical.specialNumbers.gcd_by_iterative (-3) (-9) == 3
#guard canonical.specialNumbers.gcd_by_iterative 3 (-9) == 3
#guard canonical.specialNumbers.gcd_by_iterative 100 25 == 25
#guard canonical.specialNumbers.gcd_by_iterative 17 5 == 1

-- ── ArmstrongNumbers ──────────────────────────────────────────────────────

#guard canonical.specialNumbers.armstrong_number 1 == true
#guard canonical.specialNumbers.armstrong_number 5 == true
#guard canonical.specialNumbers.armstrong_number 153 == true
#guard canonical.specialNumbers.armstrong_number 10 == false
#guard canonical.specialNumbers.armstrong_number (-1) == false
#guard canonical.specialNumbers.armstrong_number 9474 == true
#guard canonical.specialNumbers.armstrong_number 200 == false

#guard canonical.specialNumbers.pluperfect_number 1 == true
#guard canonical.specialNumbers.pluperfect_number 5 == true
#guard canonical.specialNumbers.pluperfect_number 10 == false
#guard canonical.specialNumbers.pluperfect_number 153 == true
#guard canonical.specialNumbers.pluperfect_number 9474 == true

#guard canonical.specialNumbers.narcissistic_number 1 == true
#guard canonical.specialNumbers.narcissistic_number 153 == true
#guard canonical.specialNumbers.narcissistic_number 10 == false
#guard canonical.specialNumbers.narcissistic_number 370 == true
#guard canonical.specialNumbers.narcissistic_number 371 == true

-- ── AutomorphicNumber ─────────────────────────────────────────────────────

#guard canonical.specialNumbers.is_automorphic_number 0 == true
#guard canonical.specialNumbers.is_automorphic_number 1 == true
#guard canonical.specialNumbers.is_automorphic_number 5 == true
#guard canonical.specialNumbers.is_automorphic_number 25 == true
#guard canonical.specialNumbers.is_automorphic_number 7 == false
#guard canonical.specialNumbers.is_automorphic_number (-1) == false
#guard canonical.specialNumbers.is_automorphic_number 76 == true
#guard canonical.specialNumbers.is_automorphic_number 13 == false

-- ── BellNumbers ───────────────────────────────────────────────────────────

#guard canonical.specialNumbers.bell_numbers 0 == [1]
#guard canonical.specialNumbers.bell_numbers 1 == [1, 1]
#guard canonical.specialNumbers.bell_numbers 2 == [1, 1, 2]
#guard canonical.specialNumbers.bell_numbers 3 == [1, 1, 2, 5]
#guard canonical.specialNumbers.bell_numbers 5 == [1, 1, 2, 5, 15, 52]

-- ── CarmichaelNumber ──────────────────────────────────────────────────────

#guard canonical.specialNumbers.power 2 15 3 == 2
#guard canonical.specialNumbers.power 5 1 30 == 5
#guard canonical.specialNumbers.power 3 4 5 == 1
#guard canonical.specialNumbers.power 7 0 13 == 1
#guard canonical.specialNumbers.power 2 10 1000 == 24

#guard canonical.specialNumbers.is_carmichael_number 1 == false
#guard canonical.specialNumbers.is_carmichael_number 2 == false
#guard canonical.specialNumbers.is_carmichael_number 3 == false
#guard canonical.specialNumbers.is_carmichael_number 4 == false
#guard canonical.specialNumbers.is_carmichael_number 561 == true
#guard canonical.specialNumbers.is_carmichael_number 1105 == true
#guard canonical.specialNumbers.is_carmichael_number 8 == false
#guard canonical.specialNumbers.is_carmichael_number 15 == false

-- ── CatalanNumber ─────────────────────────────────────────────────────────

#guard canonical.specialNumbers.catalan 1 == 1
#guard canonical.specialNumbers.catalan 2 == 1
#guard canonical.specialNumbers.catalan 3 == 2
#guard canonical.specialNumbers.catalan 4 == 5
#guard canonical.specialNumbers.catalan 5 == 14
#guard canonical.specialNumbers.catalan 6 == 42

-- ── HammingNumbers ────────────────────────────────────────────────────────

#guard canonical.specialNumbers.hamming 5 == [1, 2, 3, 4, 5]
#guard canonical.specialNumbers.hamming 10 == [1, 2, 3, 4, 5, 6, 8, 9, 10, 12]
#guard canonical.specialNumbers.hamming 1 == [1]
#guard canonical.specialNumbers.hamming 0 == []
#guard canonical.specialNumbers.hamming 3 == [1, 2, 3]

-- ── HappyNumber ───────────────────────────────────────────────────────────

#guard canonical.specialNumbers.is_happy_number 19 == true
#guard canonical.specialNumbers.is_happy_number 2 == false
#guard canonical.specialNumbers.is_happy_number 1 == true
#guard canonical.specialNumbers.is_happy_number 7 == true
#guard canonical.specialNumbers.is_happy_number 4 == false

-- ── HarshadNumbers ────────────────────────────────────────────────────────

#guard canonical.specialNumbers.int_to_base 0 21 == "0"
#guard canonical.specialNumbers.int_to_base 23 2 == "10111"
#guard canonical.specialNumbers.int_to_base 255 16 == "FF"
#guard canonical.specialNumbers.int_to_base 10 2 == "1010"
#guard canonical.specialNumbers.int_to_base 1 5 == "1"

#guard canonical.specialNumbers.sum_of_digits 103 12 == "13"
#guard canonical.specialNumbers.sum_of_digits 1275 4 == "30"
#guard canonical.specialNumbers.sum_of_digits 0 10 == "0"
#guard canonical.specialNumbers.sum_of_digits 9 10 == "9"
#guard canonical.specialNumbers.sum_of_digits 100 10 == "1"

#guard canonical.specialNumbers.harshad_numbers_in_base 15 2 == ["1", "10", "100", "110", "1000", "1010", "1100"]
#guard canonical.specialNumbers.harshad_numbers_in_base 12 34 == ["1", "2", "3", "4", "5", "6", "7", "8", "9", "A", "B"]
#guard canonical.specialNumbers.harshad_numbers_in_base 1 10 == []
#guard canonical.specialNumbers.harshad_numbers_in_base 11 10 == ["1", "2", "3", "4", "5", "6", "7", "8", "9", "10"]

#guard canonical.specialNumbers.is_harshad_number_in_base 18 10 == true
#guard canonical.specialNumbers.is_harshad_number_in_base 21 10 == true
#guard canonical.specialNumbers.is_harshad_number_in_base 12 10 == true
#guard canonical.specialNumbers.is_harshad_number_in_base 11 10 == false
#guard canonical.specialNumbers.is_harshad_number_in_base 1729 10 == true

-- ── HexagonalNumber ───────────────────────────────────────────────────────

#guard canonical.specialNumbers.hexagonal 1 == 1
#guard canonical.specialNumbers.hexagonal 2 == 6
#guard canonical.specialNumbers.hexagonal 3 == 15
#guard canonical.specialNumbers.hexagonal 4 == 28
#guard canonical.specialNumbers.hexagonal 0 == 0

-- ── KrishnamurthyNumber ───────────────────────────────────────────────────

#guard canonical.specialNumbers.factorial 3 == 6
#guard canonical.specialNumbers.factorial 0 == 1
#guard canonical.specialNumbers.factorial 5 == 120
#guard canonical.specialNumbers.factorial 4 == 24
#guard canonical.specialNumbers.factorial 1 == 1

#guard canonical.specialNumbers.krishnamurthy 145 == true
#guard canonical.specialNumbers.krishnamurthy 240 == false
#guard canonical.specialNumbers.krishnamurthy 1 == true
#guard canonical.specialNumbers.krishnamurthy 2 == true
#guard canonical.specialNumbers.krishnamurthy 10 == false

-- ── PerfectNumber ─────────────────────────────────────────────────────────

#guard canonical.specialNumbers.perfect 6 == true
#guard canonical.specialNumbers.perfect 28 == true
#guard canonical.specialNumbers.perfect 5 == false
#guard canonical.specialNumbers.perfect 496 == true
#guard canonical.specialNumbers.perfect 12 == false

-- ── PolygonalNumbers ──────────────────────────────────────────────────────

#guard canonical.specialNumbers.polygonal_num 0 3 == 0
#guard canonical.specialNumbers.polygonal_num 3 3 == 6
#guard canonical.specialNumbers.polygonal_num 5 4 == 25
#guard canonical.specialNumbers.polygonal_num 4 5 == 22
#guard canonical.specialNumbers.polygonal_num 2 3 == 3
#guard canonical.specialNumbers.polygonal_num (-1) 3 == 0

-- ── PronicNumber ──────────────────────────────────────────────────────────

#guard canonical.specialNumbers.is_pronic 0 == true
#guard canonical.specialNumbers.is_pronic 2 == true
#guard canonical.specialNumbers.is_pronic 5 == false
#guard canonical.specialNumbers.is_pronic 6 == true
#guard canonical.specialNumbers.is_pronic 12 == true
#guard canonical.specialNumbers.is_pronic 20 == true
#guard canonical.specialNumbers.is_pronic 7 == false

-- ── ProthNumber ───────────────────────────────────────────────────────────

#guard canonical.specialNumbers.proth 1 == 3
#guard canonical.specialNumbers.proth 2 == 5
#guard canonical.specialNumbers.proth 3 == 9
#guard canonical.specialNumbers.proth 4 == 13
#guard canonical.specialNumbers.proth 5 == 17
#guard canonical.specialNumbers.proth 6 == 25

-- ── TriangularNumbers ─────────────────────────────────────────────────────

#guard canonical.specialNumbers.triangular_number 1 == 1
#guard canonical.specialNumbers.triangular_number 3 == 6
#guard canonical.specialNumbers.triangular_number 5 == 15
#guard canonical.specialNumbers.triangular_number 10 == 55
#guard canonical.specialNumbers.triangular_number 0 == 0
#guard canonical.specialNumbers.triangular_number (-1) == 0

-- ── UglyNumbers ───────────────────────────────────────────────────────────

#guard canonical.specialNumbers.ugly_numbers 100 == 1536
#guard canonical.specialNumbers.ugly_numbers 0 == 1
#guard canonical.specialNumbers.ugly_numbers 1 == 1
#guard canonical.specialNumbers.ugly_numbers 2 == 2
#guard canonical.specialNumbers.ugly_numbers 11 == 15

-- ── WeirdNumber ───────────────────────────────────────────────────────────

#guard canonical.specialNumbers.factors 12 == [1, 2, 3, 4, 6]
#guard canonical.specialNumbers.factors 1 == [1]
#guard canonical.specialNumbers.factors 28 == [1, 2, 4, 7, 14]
#guard canonical.specialNumbers.factors 6 == [1, 2, 3]
#guard canonical.specialNumbers.factors 0 == [1]

#guard canonical.specialNumbers.abundant 0 == true
#guard canonical.specialNumbers.abundant 1 == false
#guard canonical.specialNumbers.abundant 12 == true
#guard canonical.specialNumbers.abundant 18 == true
#guard canonical.specialNumbers.abundant 7 == false

#guard canonical.specialNumbers.semi_perfect 0 == true
#guard canonical.specialNumbers.semi_perfect 1 == true
#guard canonical.specialNumbers.semi_perfect 12 == true
#guard canonical.specialNumbers.semi_perfect 6 == true
#guard canonical.specialNumbers.semi_perfect 18 == true

#guard canonical.specialNumbers.weird 0 == false
#guard canonical.specialNumbers.weird 70 == true
#guard canonical.specialNumbers.weird 12 == false
#guard canonical.specialNumbers.weird 4 == false
#guard canonical.specialNumbers.weird 18 == false
