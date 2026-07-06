import DafnyVMC.Harness
import DafnyVMC.Impl.UniformModel

/-!
# DafnyVMC.Spec.SpecUniformCorrectness

Correctness specifications for the uniform sampler `sample` and the
interval sampler `intervalSample`. These are the five primary proof-mode
theorem stubs for the LLM.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- Each outcome `i < n` has probability exactly `1/n` under `sample n hn`.
    The probability measure `prob` takes values in `ENNReal`. -/
def spec_uniformFullCorrectness (_impl : RepoImpl) : Prop :=
  ∀ (n : Nat) (hn : n > 0) (i : Nat) (hi : i < n),
    prob {s | (sample n hn s).value = i} = (1 : ENNReal) / n

/-- Each integer `i ∈ [a, b)` has probability exactly `1/(b-a)` under
    `intervalSample a b h`. -/
def spec_uniformFullIntervalCorrectness (_impl : RepoImpl) : Prop :=
  ∀ (a b i : Int) (h : a < b) (ha : a ≤ i) (hi : i < b),
    prob {s | (intervalSample a b h s).value = i} = (1 : ENNReal) / (b - a).toNat

/-- `intervalSample a b h` is a weakly independent Hurd function. -/
def spec_intervalSampleIsIndepFunction (_impl : RepoImpl) : Prop :=
  ∀ (a b : Int) (h : a < b), isIndepFunction (intervalSample a b h)

/-- The value of `intervalSample a b h s` lies in `[a, b)` for every
    bitstream `s`. -/
def spec_intervalSampleBound (_impl : RepoImpl) : Prop :=
  ∀ (a b : Int) (h : a < b) (s : Bitstream),
    a ≤ (intervalSample a b h s).value ∧ (intervalSample a b h s).value < b

/-- The rest-projection of `intervalSample a b h` is measure-preserving on
    `(Bitstream, prob)`. -/
def spec_intervalSampleIsMeasurePreserving (_impl : RepoImpl) : Prop :=
  ∀ (a b : Int) (h : a < b),
    MeasureTheory.MeasurePreserving (fun s => (intervalSample a b h s).rest) prob prob
