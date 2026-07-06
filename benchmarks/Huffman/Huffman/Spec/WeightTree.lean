import Huffman.Harness
import Huffman.Impl.WeightTree
import Huffman.Impl.Ordered

/-!
# Huffman.Spec.WeightTree

Frozen specifications translated from Coq's `WeightTree.v`.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- Coq theorem `le_sum_correct1` translated as a proof obligation. -/
def spec_le_sum_correct1 (impl : RepoImpl) : Prop :=
  ∀ (A : Type) (f : A → Nat), ∀ a b1 : BTree A,
    le_sum f a b1 = true → sum_order f a b1

/-- Coq theorem `le_sum_correct2` translated as a proof obligation. -/
def spec_le_sum_correct2 (impl : RepoImpl) : Prop :=
  ∀ (A : Type) (f : A → Nat), ∀ a b1 : BTree A,
    le_sum f a b1 = false → sum_order f b1 a

/-- Coq theorem `ordered_sum_leaves_eq` translated as a proof obligation. -/
def spec_ordered_sum_leaves_eq (impl : RepoImpl) : Prop :=
  ∀ (A : Type) (f : A → Nat) (l1 l2 : List (BTree A)),
    List.Perm l1 l2 →
    ordered (sum_order f) l1 →
    ordered (sum_order f) l2 →
    List.map (impl.huffman.sum_leaves A f) l1 =
      List.map (impl.huffman.sum_leaves A f) l2

/-- Coq theorem `weight_tree_list_node` translated as a proof obligation. -/
def spec_weight_tree_list_node (impl : RepoImpl) : Prop :=
  ∀ (A : Type) (f : A → Nat), ∀ (t1 t2 : BTree A) (l : List (BTree A)),
    impl.huffman.weight_tree_list A f (BTree.node t1 t2 :: l) =
      impl.huffman.sum_leaves A f t1 + impl.huffman.sum_leaves A f t2 +
        impl.huffman.weight_tree_list A f (t1 :: t2 :: l)

/-- Coq theorem `weight_tree_list_permutation` translated as a proof obligation. -/
def spec_weight_tree_list_permutation (impl : RepoImpl) : Prop :=
  ∀ (A : Type) (f : A → Nat), ∀ l1 l2 : List (BTree A),
    List.Perm l1 l2 →
    impl.huffman.weight_tree_list A f l1 =
      impl.huffman.weight_tree_list A f l2
