import LinkedList.Harness
import LinkedList.Spec.Aux

/-!
# LinkedList.Spec.HasLoop

Specifications for loop detection in linked lists.

The public benchmark representation is `List α`, which cannot encode
pointer identity or back edges. Within this model, a repeated value is the
intentional observable proxy for a cycle.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- hasLoop is exactly duplicate-value detection in this list model. -/
def spec_hasLoop_detects_duplicate_values (impl : RepoImpl) : Prop :=
  ∀ (l : List Int),
    impl.linkedList.hasLoop_hasLoop l = spec_helper_hasDuplicate l

/-- hasLoop and Floyd's detectCycle agree on every input (cross-module). -/
def spec_hasLoop_eq_floyd (impl : RepoImpl) : Prop :=
  ∀ (l : List Int),
    impl.linkedList.hasLoop_hasLoop l = impl.linkedList.floyd_detectCycle l
