import Huffman.Harness

/-!
# Huffman.Spec.BTree

Specifications for binary-tree traversal and code generation. Each
`spec_*` is a property over an arbitrary `impl : RepoImpl`.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- If a tree has distinct leaves, its collected leaf list has no duplicates. -/
def spec_all_leaves_NoDup (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A] (empty : A), ∀ t, distinct_leaves t → List.Nodup (impl.huffman.all_leaves A t)

/-- Every leaf in a tree appears in the collected leaf list. -/
def spec_all_leaves_in (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A] (empty : A), ∀ t a, inb (BTree.leaf a) t → a ∈ impl.huffman.all_leaves A t

/-- Every element in the collected leaf list is a leaf of the tree. -/
def spec_all_leaves_inb (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A] (empty : A), ∀ t a, a ∈ impl.huffman.all_leaves A t → inb (BTree.leaf a) t

/-- A duplicate-free collected leaf list implies distinct tree leaves. -/
def spec_all_leaves_unique (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A] (empty : A), ∀ t, List.Nodup (impl.huffman.all_leaves A t) → distinct_leaves t

/-- Prefix-related code entries identify the same tree leaf. -/
def spec_btree_unique_prefix1 (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A] (empty : A), ∀ (t : BTree A) (a1 a2 : A) (lb1 lb2 : List Bool),
    (a1, lb1) ∈ impl.huffman.compute_code A t →
    (a2, lb2) ∈ impl.huffman.compute_code A t →
    is_prefix lb1 lb2 →
    a1 = a2

/-- A tree with distinct leaves has unique code keys. -/
def spec_btree_unique_prefix2 (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A] (empty : A), ∀ t : BTree A,
    distinct_leaves t → unique_key (impl.huffman.compute_code A t)

/-- A tree with distinct leaves has a prefix-unique computed code. -/
def spec_btree_unique_prefix (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A] (empty : A), ∀ t : BTree A,
    distinct_leaves t → unique_prefix (impl.huffman.compute_code A t)

/-- Distinct leaves for a node imply distinct leaves for the left subtree. -/
def spec_distinct_leaves_l (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A] (empty : A), ∀ t1 t2 : BTree A,
    distinct_leaves (BTree.node t1 t2) → distinct_leaves t1

/-- A leaf tree has distinct leaves. -/
def spec_distinct_leaves_leaf (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A] (empty : A), ∀ a : A, distinct_leaves (BTree.leaf a)

/-- Distinct leaves for a node imply distinct leaves for the right subtree. -/
def spec_distinct_leaves_r (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A] (empty : A), ∀ t1 t2 : BTree A,
    distinct_leaves (BTree.node t1 t2) → distinct_leaves t2

/-- Every computed code entry corresponds to a leaf of the tree. -/
def spec_inCompute_inb (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A] (empty : A), ∀ (t : BTree A) (a : A) (l : List Bool),
    (a, l) ∈ impl.huffman.compute_code A t → inb (BTree.leaf a) t

/-- A list whose elements are tree leaves is included in the computed alphabet. -/
def spec_in_alphabet_compute_code (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A] (empty : A), ∀ m t,
    (∀ a : A, a ∈ m → inb (BTree.leaf a) t) →
    in_alphabet m (impl.huffman.compute_code A t)

/-- Tree membership is antisymmetric. -/
def spec_inb_antisym (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A] (empty : A), ∀ t1 t2 : BTree A,
    inb t1 t2 → inb t2 t1 → t1 = t2

/-- Every leaf in a tree has an associated computed code. -/
def spec_inb_compute_ex (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A] (empty : A), ∀ (a : A) (p : BTree A),
    inb (BTree.leaf a) p → ∃ l, (a, l) ∈ impl.huffman.compute_code A p

/-- Every tree contains some leaf. -/
def spec_inb_ex (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A] (empty : A), ∀ t : BTree A, ∃ x, inb (BTree.leaf x) t

/-- Tree membership is transitive. -/
def spec_inb_trans (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A] (empty : A), ∀ t1 t2 t3 : BTree A,
    inb t1 t2 → inb t2 t3 → inb t1 t3

/-- The computed code for a tree is nonempty. -/
def spec_length_compute_lt_O (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A] (empty : A), ∀ t : BTree A, 0 < List.length (impl.huffman.compute_code A t)

/-- Membership implies no larger node count than the containing tree. -/
def spec_number_of_nodes_inb_le (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A] (empty : A), ∀ t1 t2 : BTree A,
    inb t1 t2 → number_of_nodes t1 ≤ number_of_nodes t2
