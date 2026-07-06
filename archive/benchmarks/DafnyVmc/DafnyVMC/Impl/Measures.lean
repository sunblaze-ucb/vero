import DafnyVMC.Impl.Rand
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.Probability.Independence.Basic

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# DafnyVMC.Impl.Measures

Measure-theoretic vocabulary for DafnyVMC: type aliases for
measure-preserving maps, independent events, and preimages.
Corresponds to `src/Math/Measures.dfy`.

- `IsMeasurePreserving` aliases Mathlib's
  `MeasureTheory.MeasurePreserving`, specialised to a single carrier type `α`.
- `AreIndepEvents` aliases `ProbabilityTheory.IndepSets` specialised to
  the `Bitstream` sample space under `prob`.
- `PreImage` aliases `Set.preimage` (`f ⁻¹' s`).

These are purely vocabulary type aliases used by other DafnyVMC
modules and specs; there are no implementation stubs in this file.

DO NOT MODIFY types — these are the fixed vocabulary.
-/

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- ── Vocabulary aliases (DO NOT MODIFY) ────────────────────────────────

/-- Measure-preserving map on a measure space `α`.
    Alias of Mathlib `MeasureTheory.MeasurePreserving`.
    Corresponds to Dafny's ghost predicate `IsMeasurePreserving`. -/
-- Alias of Mathlib MeasureTheory.MeasurePreserving
abbrev IsMeasurePreserving {α : Type} [MeasurableSpace α]
    (μ ν : MeasureTheory.Measure α) (f : α → α) : Prop :=
  MeasureTheory.MeasurePreserving f μ ν

/-- Independence of two collections of sets of bitstreams under `prob`.
    Alias of Mathlib `ProbabilityTheory.IndepSets` specialised to `Bitstream`.
    Corresponds to Dafny's predicate `AreIndepEvents`. -/
-- Alias of Mathlib ProbabilityTheory.IndepSets
abbrev AreIndepEvents (s₁ s₂ : Set (Set Bitstream)) : Prop :=
  ProbabilityTheory.IndepSets s₁ s₂ prob

/-- Preimage of a set `s` under a function `f`.
    Alias of `Set.preimage` (`f ⁻¹' s`).
    Corresponds to Dafny's ghost function `PreImage`. -/
-- Alias of Set.preimage
abbrev PreImage {α β : Type} (f : α → β) (s : Set β) : Set α :=
  f ⁻¹' s
