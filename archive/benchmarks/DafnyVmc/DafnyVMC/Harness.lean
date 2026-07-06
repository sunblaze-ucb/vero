import DafnyVMC.Bundle

/-!
# DafnyVMC.Harness

Benchmark harness: `RepoImpl` structure (one field per package),
`canonical` instance wiring all API fields to their reference implementations,
and the `joint_unsat` macro.

DO NOT MODIFY — benchmark infrastructure.
-/

/-- The single-package `RepoImpl` for DafnyVMC.
    One field `dafnyVMC` holding the full `DafnyVMCBundle`. -/
structure RepoImpl where
  dafnyVMC : DafnyVMCBundle

/-- The canonical `RepoImpl` wiring each bundle field to the corresponding
    top-level function from `Impl/DafnyVMCTrait.lean`. -/
def canonical : RepoImpl where
  dafnyVMC := {
    uniformSample                   := uniformSample
    bernoulliSample                 := bernoulliSample
    bernoulliExpNegSampleUnitLoop   := bernoulliExpNegSampleUnitLoop
    bernoulliExpNegSampleUnitAux    := bernoulliExpNegSampleUnitAux
    bernoulliExpNegSampleUnit       := bernoulliExpNegSampleUnit
    bernoulliExpNegSampleGenLoop    := bernoulliExpNegSampleGenLoop
    bernoulliExpNegSample           := bernoulliExpNegSample
    discreteLaplaceSampleLoopIn1Aux := discreteLaplaceSampleLoopIn1Aux
    discreteLaplaceSampleLoopIn1    := discreteLaplaceSampleLoopIn1
    discreteLaplaceSampleLoopIn2Aux := discreteLaplaceSampleLoopIn2Aux
    discreteLaplaceSampleLoopIn2    := discreteLaplaceSampleLoopIn2
    discreteLaplaceSampleLoop       := discreteLaplaceSampleLoop
    discreteLaplaceSampleLoopPrime  := discreteLaplaceSampleLoopPrime
    discreteLaplaceSampleOptimized  := discreteLaplaceSampleOptimized
    discreteLaplaceSampleMixed      := discreteLaplaceSampleMixed
    discreteGaussianSampleLoop      := discreteGaussianSampleLoop
    discreteLaplaceSample           := discreteLaplaceSample
    discreteGaussianSample          := discreteGaussianSample
  }

/-- `joint_unsat spec_A spec_B [spec_C …] by <proof>` generates the
    ∧-conjunction unsatisfiability theorem. Variadic; no sort / no dedup —
    anti-cheat is enforced at `!solution` extraction during evaluation. -/
syntax "joint_unsat" ident ident ident* "by" tacticSeq : command

open Lean in
macro_rules
  | `(joint_unsat $s1 $s2 $[$rest]* by $proof) => do
    let specs := #[s1, s2] ++ rest
    let name := specs.foldl (init := `joint_unsat) fun acc s => Name.append acc s.getId
    let mut body ← `($(specs[0]!) impl)
    for s in specs[1:] do
      body ← `($body ∧ $s impl)
    `(theorem $(mkIdent name) : ¬ ∃ impl : RepoImpl, $body := by $proof)
