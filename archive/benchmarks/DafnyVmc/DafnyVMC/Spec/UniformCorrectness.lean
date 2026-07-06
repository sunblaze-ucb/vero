import DafnyVMC.Harness
import DafnyVMC.Impl.UniformCorrectness

/-!
# DafnyVMC.Spec.UniformCorrectness

Specifications for the uniform distribution sampler `sample`.
These three properties follow directly from the axiomatised postconditions
in `Impl/UniformModel.lean` and serve as benchmarked theorem stubs.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- `sample n h` is a weakly independent Hurd function: for every measurable
    value-set `A` and rest-set `E`, the preimage events are independent under `prob`.
    Follows from `sample_isIndepFunction` in `Impl/UniformModel.lean`. -/
def spec_sampleIsIndepFunction (_impl : RepoImpl) : Prop :=
  ∀ (n : Nat) (h : n > 0), isIndepFunction (sample n h)

/-- The value produced by `sample n h s` lies strictly below `n`
    for every bitstream `s`.
    Follows from `sample_bound` in `Impl/UniformModel.lean`. -/
def spec_sampleBound (_impl : RepoImpl) : Prop :=
  ∀ (n : Nat) (h : n > 0) (s : Bitstream), (sample n h s).value < n

/-- The rest-projection of `sample n h` is a measure-preserving map on
    `(Bitstream, prob)`.
    Follows from `sample_isMeasurePreserving` in `Impl/UniformModel.lean`. -/
def spec_sampleIsMeasurePreserving (_impl : RepoImpl) : Prop :=
  ∀ (n : Nat) (h : n > 0),
    MeasureTheory.MeasurePreserving (fun s => (sample n h s).rest) prob prob
