import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# DafnyVMC.Impl.Rand

Foundation type `Bitstream` (an infinite binary stream) and the axiomatised
probability measure `prob` for DafnyVMC.  Corresponds to
`src/ProbabilisticProgramming/RandomSource.dfy`.

- `Bitstream` is the sample space: an infinite sequence of coin-flip bits.
- `instMeasurableSpaceBitstream` provides the product σ-algebra via Mathlib's
  `MeasurableSpace.pi` instance (the canonical `Nat → Bool` product measurable space).
- `prob` is the axiomatised fair-coin product measure.
- `probIsProbabilityMeasure` asserts that `prob` has total mass 1.

DO NOT MODIFY types — these are the fixed vocabulary.
-/

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- ── Foundation types (DO NOT MODIFY) ──────────────────────────────

/-- A bitstream: an infinite sequence of bits (coin flips).
    Corresponds to Dafny's `Rand.Bitstream`. -/
abbrev Bitstream := Nat → Bool

/-- Product σ-algebra on `Bitstream` (Nat → Bool), constructed via Mathlib's
    `MeasurableSpace.pi` instance for dependent-function types. -/
instance instMeasurableSpaceBitstream : MeasurableSpace Bitstream := MeasurableSpace.pi

/-- Axiomatised fair-coin product measure on `Bitstream`.
    Corresponds to Dafny's `ghost const prob : Rand.Bitstream -> real`. -/
axiom prob : MeasureTheory.Measure Bitstream

/-- `prob` is a probability measure (`prob Set.univ = 1`).
    Corresponds to Dafny's `lemma {:axiom} ProbIsProbabilityMeasure()`. -/
axiom probIsProbabilityMeasure : MeasureTheory.IsProbabilityMeasure prob
