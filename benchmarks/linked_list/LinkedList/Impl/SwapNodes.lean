-- !benchmark @start imports
-- !benchmark @end imports

/-!
# LinkedList.Impl.SwapNodes

Swap node values in a linked list, modelled as `List α` with `BEq α`.

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
Implement only the function bodies.
-/

abbrev Swap.LinkedList (α : Type) := List α

-- !benchmark @start global_aux
-- !benchmark @end global_aux

namespace Swap

variable {α : Type}

abbrev PushSig      := List α → α → List α
abbrev SwapNodesSig := [BEq α] → List α → α → α → List α

-- !benchmark @start code_aux def=swap_push
-- !benchmark @end code_aux def=swap_push

def push : List α → α → List α :=
-- !benchmark @start code def=swap_push
  fun l a => a :: l
-- !benchmark @end code def=swap_push

-- !benchmark @start code_aux def=swap_swapNodes
-- Helper: find index of first occurrence of v.
private def findFirstIdx [BEq α] (v : α) : List α → Option Nat
  | [] => none
  | x :: xs =>
    if x == v then some 0
    else (findFirstIdx v xs).map Nat.succ

-- Helper: replace element at position i with newVal.
private def setAt (i : Nat) (newVal : α) : List α → List α
  | [] => []
  | x :: xs =>
    if i == 0 then newVal :: xs
    else x :: setAt (i - 1) newVal xs
-- !benchmark @end code_aux def=swap_swapNodes

def swapNodes [BEq α] : List α → α → α → List α :=
-- !benchmark @start code def=swap_swapNodes
  fun l x y =>
    if x == y then l
    else
      match findFirstIdx x l, findFirstIdx y l with
      | some i, some j => setAt j x (setAt i y l)
      | _, _ => l
-- !benchmark @end code def=swap_swapNodes

end Swap
