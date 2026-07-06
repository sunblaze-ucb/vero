-- !benchmark @start imports
-- !benchmark @end imports

/-!
# LinkedList.Impl.LinkedListInit

Position-based linked list init operations modelled as `List α`.

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
Implement only the function bodies.
-/

abbrev LLI.LinkedList (α : Type) := List α

-- !benchmark @start global_aux
-- !benchmark @end global_aux

namespace LLI

variable {α : Type}

abbrev AddSig     := List α → α → Nat → List α
abbrev RemoveSig  := List α → Option (α × List α)
abbrev IsEmptySig := List α → Bool
abbrev LengthSig  := List α → Nat

-- !benchmark @start code_aux def=lli_add
-- !benchmark @end code_aux def=lli_add

def add : List α → α → Nat → List α :=
-- !benchmark @start code def=lli_add
  fun l item position => l.take position ++ [item] ++ l.drop position
-- !benchmark @end code def=lli_add

-- !benchmark @start code_aux def=lli_remove
-- !benchmark @end code_aux def=lli_remove

def remove : List α → Option (α × List α) :=
-- !benchmark @start code def=lli_remove
  fun l =>
    match l with
    | []      => none
    | x :: xs => some (x, xs)
-- !benchmark @end code def=lli_remove

-- !benchmark @start code_aux def=lli_isEmpty
-- !benchmark @end code_aux def=lli_isEmpty

def isEmpty : List α → Bool :=
-- !benchmark @start code def=lli_isEmpty
  fun l => l.isEmpty
-- !benchmark @end code def=lli_isEmpty

-- !benchmark @start code_aux def=lli_length
-- !benchmark @end code_aux def=lli_length

def length : List α → Nat :=
-- !benchmark @start code def=lli_length
  fun l => l.length
-- !benchmark @end code def=lli_length

end LLI
