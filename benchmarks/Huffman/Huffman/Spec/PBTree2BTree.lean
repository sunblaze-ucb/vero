import Huffman.Harness

/-!
# Huffman.Spec.PBTree2BTree

Frozen specifications translated from Coq's `PBTree2BTree.v`. Each `spec_*`
is a property over an arbitrary `impl : RepoImpl`.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- Converting a partial binary tree preserves the list of leaves. -/
def spec_to_btree_all_leaves (impl : RepoImpl) : Prop :=
  ∀ (A : Type), ∀ t : PBTree A,
    impl.huffman.all_leaves A (impl.huffman.to_btree A t) = impl.huffman.all_pbleaves A t

/-- Distinct partial-tree leaves remain distinct after conversion to a binary tree. -/
def spec_to_btree_distinct_leaves (impl : RepoImpl) : Prop :=
  ∀ (A : Type), ∀ a : PBTree A,
    distinct_pbleaves a → distinct_leaves (impl.huffman.to_btree A a)

/-- Distinct converted binary-tree leaves imply distinct partial-tree leaves. -/
def spec_to_btree_distinct_pbleaves (impl : RepoImpl) : Prop :=
  ∀ (A : Type), ∀ a : PBTree A,
    distinct_leaves (impl.huffman.to_btree A a) → distinct_pbleaves a

/-- Partial-tree leaf membership is preserved by conversion to a binary tree. -/
def spec_to_btree_inb (impl : RepoImpl) : Prop :=
  ∀ (A : Type), ∀ a : A, ∀ b : PBTree A,
    inpb (PBTree.pbleaf a) b → inb (BTree.leaf a) (impl.huffman.to_btree A b)

/-- Converted binary-tree leaf membership reflects partial-tree membership. -/
def spec_to_btree_inpb (impl : RepoImpl) : Prop :=
  ∀ (A : Type), ∀ a : A, ∀ b : PBTree A,
    inb (BTree.leaf a) (impl.huffman.to_btree A b) → inpb (PBTree.pbleaf a) b

/-- For each key, the converted binary-tree code is no longer than the partial-tree code. -/
def spec_to_btree_smaller (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A], ∀ (t : PBTree A) (a : A),
    List.length (impl.huffman.find_code A a (impl.huffman.compute_code A (impl.huffman.to_btree A t))) ≤
      List.length (impl.huffman.find_code A a (impl.huffman.compute_pbcode A t))
