import DafnyVMC.Impl.DafnyVMCTrait

/-!
# DafnyVMC.Bundle

Per-package implementation bundle for the `DafnyVMC` root package.
Collects all API signatures from `DafnyVMCTrait` into one structure.

DO NOT MODIFY — benchmark infrastructure.
-/

/-- Bundle of all probabilistic sampler APIs from `DafnyVMCTrait`.
    The four fields with `!benchmark` markers are the primary LLM tasks;
    the remaining fields are helper stubs used by the implementation chain. -/
structure DafnyVMCBundle where
  uniformSample                   : UniformSampleSig
  bernoulliSample                 : BernoulliSampleSig
  bernoulliExpNegSampleUnitLoop   : BernoulliExpNegSampleUnitLoopSig
  bernoulliExpNegSampleUnitAux    : BernoulliExpNegSampleUnitAuxSig
  bernoulliExpNegSampleUnit       : BernoulliExpNegSampleUnitSig
  bernoulliExpNegSampleGenLoop    : BernoulliExpNegSampleGenLoopSig
  bernoulliExpNegSample           : BernoulliExpNegSampleSig
  discreteLaplaceSampleLoopIn1Aux : DiscreteLaplaceSampleLoopIn1AuxSig
  discreteLaplaceSampleLoopIn1    : DiscreteLaplaceSampleLoopIn1Sig
  discreteLaplaceSampleLoopIn2Aux : DiscreteLaplaceSampleLoopIn2AuxSig
  discreteLaplaceSampleLoopIn2    : DiscreteLaplaceSampleLoopIn2Sig
  discreteLaplaceSampleLoop       : DiscreteLaplaceSampleLoopSig
  discreteLaplaceSampleLoopPrime  : DiscreteLaplaceSampleLoopPrimeSig
  discreteLaplaceSampleOptimized  : DiscreteLaplaceSampleOptimizedSig
  discreteLaplaceSampleMixed      : DiscreteLaplaceSampleMixedSig
  discreteGaussianSampleLoop      : DiscreteGaussianSampleLoopSig
  discreteLaplaceSample           : DiscreteLaplaceSampleSig
  discreteGaussianSample          : DiscreteGaussianSampleSig
