-- !benchmark @start imports
-- !benchmark @end imports

/-!
# LinkedList.Impl.FloydsCycleDetection

Floyd's cycle detection modelled with duplicate-value check on `List α`.

@review human: pointer-identity cycle detection replaced by value-equality
duplicate check as functional proxy.

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
Implement only the function bodies.
-/

abbrev Floyd.LinkedList (α : Type) := List α

-- !benchmark @start global_aux
-- !benchmark @end global_aux

namespace Floyd

variable {α : Type} [BEq α]

abbrev AddNodeSig     := List α → α → List α
abbrev DetectCycleSig := List α → Bool

-- !benchmark @start code_aux def=floyd_addNode
-- !benchmark @end code_aux def=floyd_addNode

def addNode : List α → α → List α :=
-- !benchmark @start code def=floyd_addNode
  fun l a => l ++ [a]
-- !benchmark @end code def=floyd_addNode

-- !benchmark @start code_aux def=floyd_detectCycle
-- Helper: check for any duplicate element.
private def anyDuplicate : List α → Bool
  | [] => false
  | x :: xs => xs.any (· == x) || anyDuplicate xs
-- !benchmark @end code_aux def=floyd_detectCycle

def detectCycle : List α → Bool :=
-- !benchmark @start code def=floyd_detectCycle
  fun l => anyDuplicate l
-- !benchmark @end code def=floyd_detectCycle

end Floyd
