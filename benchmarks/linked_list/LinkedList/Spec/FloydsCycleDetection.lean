import LinkedList.Harness
import LinkedList.Spec.Aux

/-!
# LinkedList.Spec.FloydsCycleDetection

Specifications for Floyd's cycle detection operations.

The public benchmark representation is `List α`, which cannot encode
pointer identity or back edges. Within this model, a repeated value is the
intentional observable proxy for a cycle.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- floyd_addNode appends the element to the end, implementing snoc. -/
def spec_floyd_addNode_snoc (impl : RepoImpl) : Prop :=
  ∀ (l : List Int) (a : Int), impl.linkedList.floyd_addNode l a = l ++ [a]

/-- detectCycle is exactly duplicate-value detection in this list model. -/
def spec_floyd_detectCycle_detects_duplicate_values (impl : RepoImpl) : Prop :=
  ∀ (l : List Int),
    impl.linkedList.floyd_detectCycle l = spec_helper_hasDuplicate l

/-- floyd_detectCycle and hasLoop agree on every input (cross-module). -/
def spec_floyd_detectCycle_eq_hasLoop (impl : RepoImpl) : Prop :=
  ∀ (l : List Int),
    impl.linkedList.floyd_detectCycle l = impl.linkedList.hasLoop_hasLoop l
