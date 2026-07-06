import Huffman.Impl.BTree
import Huffman.Impl.Ordered

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Huffman.Impl.WeightTree

Weight functions over binary trees translated from Coq's `WeightTree.v`.
The executable reference implementations below compute leaf-weight sums
and total tree/list weights.

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
Implement only the function bodies.
-/

namespace Huffman

abbrev SumLeavesSig := (A : Type) → (A → Nat) → BTree A → Nat
abbrev WeightTreeSig := (A : Type) → (A → Nat) → BTree A → Nat
abbrev WeightTreeListSig := (A : Type) → (A → Nat) → List (BTree A) → Nat

end Huffman

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- !benchmark @start code_aux def=sum_leaves
-- !benchmark @end code_aux def=sum_leaves

def Huffman.sum_leaves : Huffman.SumLeavesSig :=
-- !benchmark @start code def=sum_leaves
  fun A f t =>
    let rec go : BTree A → Nat
      | BTree.leaf a => f a
      | BTree.node t1 t2 => go t1 + go t2
    go t
-- !benchmark @end code def=sum_leaves

def le_sum {A : Type} (f : A → Nat) (x y : BTree A) : Bool :=
  decide (Huffman.sum_leaves A f x ≤ Huffman.sum_leaves A f y)

def sum_order {A : Type} (f : A → Nat) (x y : BTree A) : Prop :=
  Huffman.sum_leaves A f x ≤ Huffman.sum_leaves A f y

-- !benchmark @start code_aux def=weight_tree
-- !benchmark @end code_aux def=weight_tree

def Huffman.weight_tree : Huffman.WeightTreeSig :=
-- !benchmark @start code def=weight_tree
  fun A f t =>
    let rec go : BTree A → Nat
      | BTree.leaf _ => 0
      | BTree.node t1 t2 =>
          Huffman.sum_leaves A f t1 + go t1 +
            (Huffman.sum_leaves A f t2 + go t2)
    go t
-- !benchmark @end code def=weight_tree

-- !benchmark @start code_aux def=weight_tree_list
-- !benchmark @end code_aux def=weight_tree_list

def Huffman.weight_tree_list : Huffman.WeightTreeListSig :=
-- !benchmark @start code def=weight_tree_list
  fun A f l =>
    l.foldr (fun t acc => Huffman.weight_tree A f t + acc) 0
-- !benchmark @end code def=weight_tree_list
