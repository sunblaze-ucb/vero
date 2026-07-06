import Huffman.Impl.BTree
import Huffman.Impl.Weight
import Huffman.Impl.Code
import Huffman.Impl.WeightTree
import Huffman.Impl.Cover
import Huffman.Impl.OrderedCover
import Huffman.Impl.Build
import Huffman.Impl.Prod2List
import Huffman.Impl.Frequency

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Huffman.Impl.HeightPred

Height-list predicate vocabulary translated from Coq's `HeightPred.v`.
This module has no scored API slots; the definitions below are frozen
vocabulary used by downstream specifications.
-/

inductive height_pred {A : Type} : Nat → List Nat → List (BTree A) → BTree A → Prop where
  | height_pred_nil : ∀ (n : Nat) (t : BTree A), height_pred n [n] [t] t
  | height_pred_node : ∀ (n : Nat) (ln1 ln2 : List Nat) (t1 t2 : BTree A) (l1 l2 : List (BTree A)),
      height_pred (n+1) ln1 l1 t1 → height_pred (n+1) ln2 l2 t2 →
      height_pred n (ln1 ++ ln2) (l1 ++ l2) (BTree.node t1 t2)

def helper_height_pred_disj_larger2_aux : Prop :=
  ∀ (A : Type) (f : A → Nat), ∀ (n : Nat) (ln : List Nat) (t : BTree A) (l : List (BTree A)),
    height_pred n ln l t →
      ∀ ln1 ln2 a,
        ln = ln1 ++ a :: ln2 →
          (∃ n1, n1 ∈ ln1 ∧ a ≤ n1) ∨
            (∃ n1, n1 ∈ ln2 ∧ a ≤ n1) ∨
              ln = n :: [] ∧ l = t :: []

def helper_height_pred_disj_larger_aux : Prop :=
  ∀ (A : Type) (f : A → Nat), ∀ (n : Nat) (ln : List Nat) (t : BTree A) (l : List (BTree A)),
    height_pred n ln l t →
      ∀ ln1 ln2 a,
        ln = ln1 ++ a :: ln2 →
          (∀ n1 : Nat, n1 ∈ ln1 → n1 < a) →
            (∀ n1 : Nat, n1 ∈ ln2 → n1 ≤ a) →
              (∃ ln3, ln2 = a :: ln3) ∨ ln = n :: [] ∧ l = t :: []

def helper_height_pred_shrink_aux : Prop :=
  ∀ (A : Type) (f : A → Nat), ∀ (n : Nat) (ln : List Nat) (t : BTree A) (l : List (BTree A)),
    height_pred n ln l t →
      ∀ (l1 l2 : List (BTree A)) (ln1 ln2 : List Nat) (a b : Nat) (t1 t2 : BTree A),
        ln = ln1 ++ a :: b :: ln2 →
          (∀ n1 : Nat, n1 ∈ ln1 → n1 < a) →
            (∀ n1 : Nat, n1 ∈ (b :: ln2) → n1 ≤ a) →
              List.length ln1 = List.length l1 →
                l = l1 ++ t1 :: t2 :: l2 →
                  height_pred n (ln1 ++ Nat.pred a :: ln2) (l1 ++ BTree.node t1 t2 :: l2) t

namespace Huffman

end Huffman

-- !benchmark @start global_aux
-- !benchmark @end global_aux
