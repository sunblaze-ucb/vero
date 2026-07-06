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

/-!
# SpecialNumbers.Bundle

Per-package implementation bundle for the `SpecialNumbers` root package.
Collects all 29 API signatures into one structure.

DO NOT MODIFY — benchmark infrastructure.
-/

structure SpecialNumbersBundle where
  -- GreatestCommonDivisor
  greatest_common_divisor   : SpecialNumbers.GreatestCommonDivisorSig
  gcd_by_iterative          : SpecialNumbers.GcdByIterativeSig
  -- ArmstrongNumbers
  armstrong_number          : SpecialNumbers.ArmstrongNumberSig
  pluperfect_number         : SpecialNumbers.PluperfectNumberSig
  narcissistic_number       : SpecialNumbers.NarcissisticNumberSig
  -- AutomorphicNumber
  is_automorphic_number     : SpecialNumbers.IsAutomorphicNumberSig
  -- BellNumbers
  bell_numbers              : SpecialNumbers.BellNumbersSig
  -- CarmichaelNumber
  power                     : SpecialNumbers.PowerSig
  is_carmichael_number      : SpecialNumbers.IsCarmichaelNumberSig
  -- CatalanNumber
  catalan                   : SpecialNumbers.CatalanSig
  -- HammingNumbers
  hamming                   : SpecialNumbers.HammingSig
  -- HappyNumber
  is_happy_number           : SpecialNumbers.IsHappyNumberSig
  -- HarshadNumbers
  int_to_base               : SpecialNumbers.IntToBaseSig
  sum_of_digits             : SpecialNumbers.SumOfDigitsSig
  harshad_numbers_in_base   : SpecialNumbers.HarshadNumbersInBaseSig
  is_harshad_number_in_base : SpecialNumbers.IsHarshadNumberInBaseSig
  -- HexagonalNumber
  hexagonal                 : SpecialNumbers.HexagonalSig
  -- KrishnamurthyNumber
  factorial                 : SpecialNumbers.FactorialSig
  krishnamurthy             : SpecialNumbers.KrishnamurthySig
  -- PerfectNumber
  perfect                   : SpecialNumbers.PerfectSig
  -- PolygonalNumbers
  polygonal_num             : SpecialNumbers.PolygonalNumSig
  -- PronicNumber
  is_pronic                 : SpecialNumbers.IsPronicSig
  -- ProthNumber
  proth                     : SpecialNumbers.ProthSig
  -- TriangularNumbers
  triangular_number         : SpecialNumbers.TriangularNumberSig
  -- UglyNumbers
  ugly_numbers              : SpecialNumbers.UglyNumbersSig
  -- WeirdNumber
  factors                   : SpecialNumbers.FactorsSig
  abundant                  : SpecialNumbers.AbundantSig
  semi_perfect              : SpecialNumbers.SemiPerfectSig
  weird                     : SpecialNumbers.WeirdSig
