import Huffman.Impl.BTree
import Huffman.Impl.AuxLib

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Huffman.Impl.Cover

Tree-cover vocabulary and executable cover enumeration helpers translated from
Coq's `Cover.v`. This module has no scored API slots; the definitions below
are frozen vocabulary used by downstream specifications.
-/

inductive cover {A : Type} : List (BTree A) → BTree A → Prop where
  | cover_leaf : ∀ a : A, cover [BTree.leaf a] (BTree.leaf a)
  | cover_node :
      ∀ (l1 l2 : List (BTree A)) (t1 t2 : BTree A),
        cover l1 t1 → cover l2 t2 → cover (l1 ++ l2) (BTree.node t1 t2)

def all_cover_aux {A : Type} (l : List (BTree A)) : Nat → List (BTree A)
  | 0 => []
  | n + 1 =>
      (all_permutations l).flatMap (fun l1 =>
        match l1 with
        | [] => []
        | [a] => [a]
        | a :: b :: rest => all_cover_aux (BTree.node a b :: rest) n)

def all_cover {A : Type} (l : List (BTree A)) : List (BTree A) :=
  all_cover_aux l l.length

def helper_cover_all_cover_aux : Prop :=
  ∀ (A : Type), ∀ (n : Nat) (l : List (BTree A)) (t : BTree A),
    n = List.length l → cover l t → t ∈ all_cover_aux l n

def helper_cover_inv_app_aux : Prop :=
  ∀ (A : Type), ∀ (t t1 t2 : BTree A) (l : List (BTree A)),
    cover l t →
    t = BTree.node t1 t2 →
    l = BTree.node t1 t2 :: [] ∨
      (∃ l1 : List (BTree A),
        ∃ l2 : List (BTree A),
          (cover l1 t1 ∧ cover l2 t2) ∧ List.Perm l (l1 ++ l2))

def helper_cover_inv_leaf_aux : Prop :=
  ∀ (A : Type), ∀ (t : BTree A) (l : List (BTree A)),
    cover l t → ∀ a : A, t = BTree.leaf a → l = BTree.leaf a :: []

namespace Huffman

end Huffman

-- !benchmark @start global_aux
-- !benchmark @end global_aux
