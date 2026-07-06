import DafnyVMC.Impl.Monad
import Mathlib.Probability.Independence.Basic

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# DafnyVMC.Impl.Independence

Independence predicates for Hurd probabilistic computations.
Corresponds to `src/ProbabilisticProgramming/Independence.dfy` (Definition 33).

- `isIndepFunctionCondition` holds when the set of bitstreams whose Hurd
  value falls in `A` and the set of bitstreams whose Hurd rest falls in `E`
  are independent under `prob`.
- `isIndepFunction` (weak independence) universally quantifies
  `isIndepFunctionCondition` over all value-sets and rest-sets.

These predicates are vocabulary used by correctness specs of sampling
functions in other DafnyVMC modules.

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
Implement only the function bodies.
-/

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- ── Independence predicates (LLM task) ─────────────────────────────

-- !benchmark @start code_aux def=isIndepFunctionCondition
-- !benchmark @end code_aux def=isIndepFunctionCondition

def isIndepFunctionCondition {α : Type} [MeasurableSpace α]
    (f : Hurd α) (A : Set α) (E : Set Bitstream) : Prop :=
-- !benchmark @start code def=isIndepFunctionCondition
  ProbabilityTheory.IndepSets
    {bitstreamsWithValueIn f A}
    {bitstreamsWithRestIn f E}
    prob
-- !benchmark @end code def=isIndepFunctionCondition

-- !benchmark @start code_aux def=isIndepFunction
-- !benchmark @end code_aux def=isIndepFunction

def isIndepFunction {α : Type} [MeasurableSpace α] (f : Hurd α) : Prop :=
-- !benchmark @start code def=isIndepFunction
  ∀ (A : Set α) (E : Set Bitstream), isIndepFunctionCondition f A E
-- !benchmark @end code def=isIndepFunction
