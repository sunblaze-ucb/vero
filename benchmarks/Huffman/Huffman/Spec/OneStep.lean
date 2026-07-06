import Huffman.Harness
import Huffman.Impl.OneStep

/-!
# Huffman.Spec.OneStep

Frozen specifications translated from Coq's `OneStep.v`.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- Coq theorem `one_step_comp` translated as a proof obligation. -/
def spec_one_step_comp (impl : RepoImpl) : Prop :=
  ∀ (A : Type) (f : A → Nat), ∀ l1 l2 l3 l4 : List (BTree A),
    impl.huffman.weight_tree_list A f l1 = impl.huffman.weight_tree_list A f l2 →
    same_sum_leaves f l1 l2 →
    one_step f l1 l3 →
    one_step f l2 l4 →
    impl.huffman.weight_tree_list A f l3 = impl.huffman.weight_tree_list A f l4 ∧
      same_sum_leaves f l3 l4

/-- Coq theorem `one_step_same_sum_leaves` translated as a proof obligation. -/
def spec_one_step_same_sum_leaves (impl : RepoImpl) : Prop :=
  ∀ (A : Type) (f : A → Nat), ∀ l1 l2 l3 : List (BTree A),
    one_step f l1 l2 →
    one_step f l1 l3 →
    same_sum_leaves f l2 l3

/-- Coq theorem `one_step_weight_tree_list` translated as a proof obligation. -/
def spec_one_step_weight_tree_list (impl : RepoImpl) : Prop :=
  ∀ (A : Type) (f : A → Nat), ∀ l1 l2 l3 : List (BTree A),
    one_step f l1 l2 →
    one_step f l1 l3 →
    impl.huffman.weight_tree_list A f l2 = impl.huffman.weight_tree_list A f l3
