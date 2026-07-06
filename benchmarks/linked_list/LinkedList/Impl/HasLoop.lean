-- !benchmark @start imports
-- !benchmark @end imports

/-!
# LinkedList.Impl.HasLoop

Loop detection. `List α` cannot have pointer cycles; `hasLoop` detects
duplicate values as a proxy for loop detection.

@review human: Python's loop detection uses object identity; we use value
equality via `BEq α` as proxy.

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
Implement only the function bodies.
-/

abbrev HasLoop.Node (α : Type) := List α

-- !benchmark @start global_aux
-- !benchmark @end global_aux

namespace HasLoop

variable {α : Type} [BEq α]

abbrev HasLoopSig := List α → Bool

-- !benchmark @start code_aux def=hasLoop_hasLoop
-- Helper: check for duplicate elements.
private def hasDuplicate : List α → Bool
  | [] => false
  | x :: xs => xs.any (· == x) || hasDuplicate xs
-- !benchmark @end code_aux def=hasLoop_hasLoop

def hasLoop : List α → Bool :=
-- !benchmark @start code def=hasLoop_hasLoop
  fun l => hasDuplicate l
-- !benchmark @end code def=hasLoop_hasLoop

end HasLoop
