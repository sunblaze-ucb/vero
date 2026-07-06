import Huffman.Impl.WeightTree
import Huffman.Impl.Ordered
import Huffman.Impl.BTree

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Huffman.Impl.Prod2List

Products between a list of natural-number coefficients and a list of
weighted binary trees translated from Coq's `Prod2List.v`.

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
Implement only the function bodies.
-/

namespace Huffman

abbrev Prod2listSig := (A : Type) → (A → Nat) → List Nat → List (BTree A) → Nat

end Huffman

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- !benchmark @start code_aux def=prod2list
-- !benchmark @end code_aux def=prod2list

def Huffman.prod2list : Huffman.Prod2listSig :=
-- !benchmark @start code def=prod2list
  fun A f l1 l2 =>
    let rec terms : List Nat → List (BTree A) → List Nat
      | [], _ => []
      | _, [] => []
      | a :: rest1, b :: rest2 =>
          (a * Huffman.sum_leaves A f b + Huffman.weight_tree A f b) :: terms rest1 rest2
    (terms l1 l2).foldl (fun acc n => acc + n) 0
-- !benchmark @end code def=prod2list
