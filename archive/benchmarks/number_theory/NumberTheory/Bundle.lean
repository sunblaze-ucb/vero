import NumberTheory.Impl.GreatestCommonDivisor
import NumberTheory.Impl.GcdOfNNumbers
import NumberTheory.Impl.LeastCommonMultiple
import NumberTheory.Impl.ExtendedEuclideanAlgorithm
import NumberTheory.Impl.ChineseRemainderTheorem

/-!
# NumberTheory.Bundle

Per-package implementation bundle for the `NumberTheory` root package.
Collects all 9 API signatures into one structure.

DO NOT MODIFY — benchmark infrastructure.
-/

structure NumberTheoryBundle where
  greatest_common_divisor        : NT.GreatestCommonDivisorSig
  gcd_by_iterative               : NT.GcdByIterativeSig
  get_factors                    : NT.GetFactorsSig
  get_greatest_common_divisor    : NT.GetGreatestCommonDivisorSig
  least_common_multiple_slow     : NT.LeastCommonMultipleSlowSig
  least_common_multiple_fast     : NT.LeastCommonMultipleFastSig
  extended_euclidean_algorithm   : NT.ExtendedEuclideanAlgorithmSig
  extended_euclid                : NT.ExtendedEuclidSig
  chinese_remainder_theorem      : NT.ChineseRemainderTheoremSig
  invert_modulo                  : NT.InvertModuloSig
  chinese_remainder_theorem2     : NT.ChineseRemainderTheorem2Sig
