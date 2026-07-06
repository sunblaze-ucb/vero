import DafnyVMC.Impl.Independence

/-!
# DafnyVMC.Spec.Independence

Vocabulary predicates `isIndepFunctionCondition` and `isIndepFunction` are
defined in `Impl/Independence.lean` and serve as building blocks for
correctness proofs of sampling functions in other DafnyVMC modules.

`isIndepFunctionCondition f A E` expresses that the preimage of `A` under
the value projection of `f` and the preimage of `E` under the rest projection
of `f` are independent events under `prob` (Definition 33 from the Dafny
source).

`isIndepFunction f` universally quantifies this condition, expressing that
the consumed bits and the produced value of `f` are probabilistically
independent for all measurable sets.

The Dafny `ResultsIndependent` and `AreIndepEventsConjunctElimination`
lemmas are theorems about these predicates that follow from the Mathlib
`MeasureTheory.IndepSets` API; they are not exposed as `spec_*` entries
here because they hold as immediate consequences of the vocabulary
definitions and do not constitute independent benchmark tasks.

DO NOT MODIFY — this file is frozen curator-given content.
-/
