import Huffman.Harness
import Huffman.Impl.Build

/-!
# Huffman.Spec.Build

Frozen specifications translated from Coq's `Build.v`.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- Coq theorem `build_comp` translated as a proof obligation. -/
def spec_build_comp (impl : RepoImpl) : Prop :=
  ∀ (A : Type) (f : A → Nat), ∀ (l1 l2 : List (BTree A)) (t1 t2 : BTree A),
    build f l1 t1 →
    build f l2 t2 →
    impl.huffman.weight_tree_list A f l1 = impl.huffman.weight_tree_list A f l2 →
    same_sum_leaves f l1 l2 →
    impl.huffman.weight_tree A f t1 = impl.huffman.weight_tree A f t2

/-- Coq theorem `build_correct` translated as a proof obligation. -/
def spec_build_correct (impl : RepoImpl) : Prop :=
  ∀ (A : Type) (f : A → Nat), ∀ (l : List (BTree A)) (t : BTree A),
    l ≠ [] → build f l t → cover_min _ f l t

/-- Coq theorem `build_cover` translated as a proof obligation. -/
def spec_build_cover (impl : RepoImpl) : Prop :=
  ∀ (A : Type) (f : A → Nat), ∀ l t, build f l t → cover l t

/-- Coq theorem `build_permutation` translated as a proof obligation. -/
def spec_build_permutation (impl : RepoImpl) : Prop :=
  ∀ (A : Type) (f : A → Nat), ∀ (l1 l2 : List (BTree A)) (t : BTree A),
    build f l1 t → List.Perm l1 l2 → build f l2 t

/-- Coq theorem `build_same_weight_tree` translated as a proof obligation. -/
def spec_build_same_weight_tree (impl : RepoImpl) : Prop :=
  ∀ (A : Type) (f : A → Nat), ∀ (l : List (BTree A)) (t1 t2 : BTree A),
    build f l t1 →
    build f l t2 →
    impl.huffman.weight_tree A f t1 = impl.huffman.weight_tree A f t2
