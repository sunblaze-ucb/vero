import DafnyVMC.Impl.Pos
import DafnyVMC.Impl.UniformPowerOfTwo

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# DafnyVMC.Impl.DafnyVMCTrait

Probabilistic samplers from `src/DafnyVMCTrait.dfy`: uniform,
Bernoulli, Bernoulli-exp-negative, discrete Laplace, and discrete
Gaussian distributions, all implemented in the Hurd monad.

The Dafny source defines these as methods on a `trait RandomTrait`.
Here they are translated as top-level functions using `bind`/`map`
over `Hurd α` (= `Bitstream → Result α`).  Rejection-sampling loops
(`while`/`decreases *` in Dafny) become `partial def` in Lean.

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
Implement only the function bodies.
-/

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- Inhabited instances required for partial def compilation
-- (partial def needs Nonempty of the return type).
private instance {α : Type} [Inhabited α] : Inhabited (Result α) :=
  ⟨⟨default, fun _ => false⟩⟩

-- ── API signatures (no markers — fixed vocabulary) ────────────────────

abbrev UniformSampleSig := Pos → Hurd Nat

abbrev BernoulliSampleSig := (num : Nat) → (den : Pos) → num ≤ den.val → Hurd Bool

abbrev BernoulliExpNegSampleUnitLoopSig := Nat → Pos → Bool × Pos → Hurd (Bool × Pos)

abbrev BernoulliExpNegSampleUnitAuxSig := Nat → Pos → Hurd Nat

abbrev BernoulliExpNegSampleUnitSig := Nat → Pos → Hurd Bool

abbrev BernoulliExpNegSampleGenLoopSig := Nat → Hurd Bool

abbrev BernoulliExpNegSampleSig := Nat → Pos → Hurd Bool

abbrev DiscreteLaplaceSampleLoopIn1AuxSig := Pos → Hurd (Nat × Bool)

abbrev DiscreteLaplaceSampleLoopIn1Sig := Pos → Hurd Nat

abbrev DiscreteLaplaceSampleLoopIn2AuxSig := Nat → Pos → Bool × Nat → Hurd (Bool × Nat)

abbrev DiscreteLaplaceSampleLoopIn2Sig := Nat → Pos → Hurd Nat

abbrev DiscreteLaplaceSampleLoopSig := Pos → Pos → Hurd (Bool × Nat)

abbrev DiscreteLaplaceSampleLoopPrimeSig := Pos → Pos → Hurd (Bool × Nat)

abbrev DiscreteLaplaceSampleOptimizedSig := Pos → Pos → Hurd Int

abbrev DiscreteLaplaceSampleMixedSig := Pos → Pos → Nat → Hurd Int

abbrev DiscreteGaussianSampleLoopSig := Pos → Pos → Pos → Nat → Hurd (Int × Bool)

abbrev DiscreteLaplaceSampleSig := Pos → Pos → Hurd Int

abbrev DiscreteGaussianSampleSig := Pos → Pos → Nat → Hurd Int

-- ── Implementation stubs (LLM task) ────────────────────────────────────

-- !benchmark @start code_aux def=uniformSample
-- !benchmark @end code_aux def=uniformSample

partial def uniformSample : UniformSampleSig := fun n =>
-- !benchmark @start code def=uniformSample
  bind (uniformPowerOfTwoSample (2 * n.val) (by omega)) fun x =>
    if x < n.val then return' x else uniformSample n
-- !benchmark @end code def=uniformSample

-- !benchmark @start code_aux def=bernoulliSample
-- !benchmark @end code_aux def=bernoulliSample

def bernoulliSample : BernoulliSampleSig := fun num den _ =>
-- !benchmark @start code def=bernoulliSample
  map (uniformSample den) fun d => decide (d < num)
-- !benchmark @end code def=bernoulliSample

def bernoulliExpNegSampleUnitLoop : BernoulliExpNegSampleUnitLoopSig := sorry

def bernoulliExpNegSampleUnitAux : BernoulliExpNegSampleUnitAuxSig := sorry

def bernoulliExpNegSampleUnit : BernoulliExpNegSampleUnitSig := sorry

def bernoulliExpNegSampleGenLoop : BernoulliExpNegSampleGenLoopSig := sorry

def bernoulliExpNegSample : BernoulliExpNegSampleSig := sorry

def discreteLaplaceSampleLoopIn1Aux : DiscreteLaplaceSampleLoopIn1AuxSig := sorry

def discreteLaplaceSampleLoopIn1 : DiscreteLaplaceSampleLoopIn1Sig := sorry

def discreteLaplaceSampleLoopIn2Aux : DiscreteLaplaceSampleLoopIn2AuxSig := sorry

def discreteLaplaceSampleLoopIn2 : DiscreteLaplaceSampleLoopIn2Sig := sorry

def discreteLaplaceSampleLoop : DiscreteLaplaceSampleLoopSig := sorry

def discreteLaplaceSampleLoopPrime : DiscreteLaplaceSampleLoopPrimeSig := sorry

def discreteLaplaceSampleOptimized : DiscreteLaplaceSampleOptimizedSig := sorry

def discreteLaplaceSampleMixed : DiscreteLaplaceSampleMixedSig := sorry

def discreteGaussianSampleLoop : DiscreteGaussianSampleLoopSig := sorry

-- !benchmark @start code_aux def=discreteLaplaceSample
-- !benchmark @end code_aux def=discreteLaplaceSample

partial def discreteLaplaceSample : DiscreteLaplaceSampleSig := fun num den =>
-- !benchmark @start code def=discreteLaplaceSample
  bind (discreteLaplaceSampleLoop num den) fun (b, v) =>
    if b && v == 0 then discreteLaplaceSample num den
    else return' (if b then -((v : Int)) else (v : Int))
-- !benchmark @end code def=discreteLaplaceSample

-- !benchmark @start code_aux def=discreteGaussianSample
-- !benchmark @end code_aux def=discreteGaussianSample

partial def discreteGaussianSample : DiscreteGaussianSampleSig := fun num den mix =>
-- !benchmark @start code def=discreteGaussianSample
  let ti : Nat  := num.val / den.val
  let t   : Pos := ⟨ti + 1, Nat.succ_pos ti⟩
  let num2 : Pos := ⟨num.val * num.val, Nat.mul_pos num.2 num.2⟩
  let den2 : Pos := ⟨den.val * den.val, Nat.mul_pos den.2 den.2⟩
  bind (discreteGaussianSampleLoop num2 den2 t mix) fun (y, c) =>
    if c then return' y else discreteGaussianSample num den mix
-- !benchmark @end code def=discreteGaussianSample
