import Huffman.Harness

/-!
# Huffman.Spec.PBTree

Frozen specifications translated from Coq's `PBTree.v`. Each `spec_*` is a
property over an arbitrary `impl : RepoImpl`.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- Adding a fresh leaf preserves duplicate-freedom of collected leaves. -/
def spec_NoDup_pbadd_prop2 (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A] (empty : A), ∀ (a1 : A) (l1 : List Bool) (t : PBTree A),
    ¬ inpb (PBTree.pbleaf a1) t →
    List.Nodup (impl.huffman.all_pbleaves A t) →
    List.Nodup (impl.huffman.all_pbleaves A (impl.huffman.pbadd A a1 t l1))

/-- A tree with distinct partial-binary leaves has no duplicate collected leaves. -/
def spec_all_pbleaves_NoDup (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A] (empty : A), ∀ t : PBTree A,
    distinct_pbleaves t → List.Nodup (impl.huffman.all_pbleaves A t)

/-- The keys of the computed code are a permutation of the collected leaves. -/
def spec_all_pbleaves_compute_pb (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A] (empty : A), ∀ t : PBTree A,
    List.Perm (List.map (fun p : A × List Bool => p.1) (impl.huffman.compute_pbcode A t))
      (impl.huffman.all_pbleaves A t)

/-- Every leaf in the tree appears in the collected leaf list. -/
def spec_all_pbleaves_in (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A] (empty : A), ∀ (t : PBTree A) (a : A),
    inpb (PBTree.pbleaf a) t → a ∈ impl.huffman.all_pbleaves A t

/-- Every collected leaf appears in the tree. -/
def spec_all_pbleaves_inpb (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A] (empty : A), ∀ (t : PBTree A) (a : A),
    a ∈ impl.huffman.all_pbleaves A t → inpb (PBTree.pbleaf a) t

/-- Leaves after insertion are either the inserted leaf or old leaves. -/
def spec_all_pbleaves_pbadd (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A] (empty : A), ∀ (l1 : List Bool) (a1 a2 : A) (t : PBTree A),
    a2 ∈ impl.huffman.all_pbleaves A (impl.huffman.pbadd A a1 t l1) →
    a2 = a1 ∨ a2 ∈ impl.huffman.all_pbleaves A t

/-- Building a tree from a prefix-unique code preserves the code keys as leaves. -/
def spec_all_pbleaves_pbbuild (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A] (empty : A), ∀ c : Code A,
    c ≠ [] →
    unique_prefix c →
    List.Perm (List.map (fun p : A × List Bool => p.1) c)
      (impl.huffman.all_pbleaves A (impl.huffman.pbbuild A empty c))

/-- Adding to a leaf creates exactly the inserted singleton leaf list. -/
def spec_all_pbleaves_pbleaf (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A] (empty : A), ∀ (l : List Bool) (a1 a2 : A),
    impl.huffman.all_pbleaves A (impl.huffman.pbadd A a1 (PBTree.pbleaf a2) l) = [a1]

/-- Duplicate-free collected leaves imply distinct partial-binary leaves. -/
def spec_all_pbleaves_unique (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A] (empty : A), ∀ t : PBTree A,
    List.Nodup (impl.huffman.all_pbleaves A t) → distinct_pbleaves t

/-- Computing a code from a partial binary tree is nonempty. -/
def spec_compute_pbcode_not_null (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A] (empty : A), ∀ p : PBTree A,
    impl.huffman.compute_pbcode A p ≠ []

/-- A single leaf has distinct leaves. -/
def spec_distinct_pbleaves_Leaf (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A] (empty : A), ∀ a : A,
    distinct_pbleaves (PBTree.pbleaf a)

/-- Distinct leaves for a node imply distinct leaves for the left subtree. -/
def spec_distinct_pbleaves_l (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A] (empty : A), ∀ t1 t2 : PBTree A,
    distinct_pbleaves (PBTree.pbnode t1 t2) → distinct_pbleaves t1

/-- Adding to a leaf creates a tree with distinct leaves. -/
def spec_distinct_pbleaves_pbadd_prop1 (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A] (empty : A), ∀ (a a1 : A) (l1 : List Bool),
    distinct_pbleaves (impl.huffman.pbadd A a1 (PBTree.pbleaf a) l1)

/-- Adding a fresh leaf preserves distinct leaves. -/
def spec_distinct_pbleaves_pbadd_prop2 (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A] (empty : A), ∀ (a1 : A) (l1 : List Bool) (t : PBTree A),
    ¬ inpb (PBTree.pbleaf a1) t →
    distinct_pbleaves t →
    distinct_pbleaves (impl.huffman.pbadd A a1 t l1)

/-- A leaf tree has distinct leaves. -/
def spec_distinct_pbleaves_pbleaf (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A] (empty : A), ∀ a : A,
    distinct_pbleaves (PBTree.pbleaf a)

/-- Wrapping a tree on the left preserves distinct leaves. -/
def spec_distinct_pbleaves_pbleft (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A] (empty : A), ∀ t : PBTree A,
    distinct_pbleaves t → distinct_pbleaves (PBTree.pbleft t)

/-- Wrapping a tree on the right preserves distinct leaves. -/
def spec_distinct_pbleaves_pbright (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A] (empty : A), ∀ t : PBTree A,
    distinct_pbleaves t → distinct_pbleaves (PBTree.pbright t)

/-- Distinct leaves for a left wrapper imply distinct leaves for its subtree. -/
def spec_distinct_pbleaves_pl (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A] (empty : A), ∀ t1 : PBTree A,
    distinct_pbleaves (PBTree.pbleft t1) → distinct_pbleaves t1

/-- Distinct leaves for a right wrapper imply distinct leaves for its subtree. -/
def spec_distinct_pbleaves_pr (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A] (empty : A), ∀ t1 : PBTree A,
    distinct_pbleaves (PBTree.pbright t1) → distinct_pbleaves t1

/-- Distinct leaves for a node imply distinct leaves for the right subtree. -/
def spec_distinct_pbleaves_r (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A] (empty : A), ∀ t1 t2 : PBTree A,
    distinct_pbleaves (PBTree.pbnode t1 t2) → distinct_pbleaves t2

/-- Adding false-prefixed codes folds into a left wrapper. -/
def spec_fold_pbadd_prop_left (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A] (empty : A), ∀ (l : Code A) (a : A),
    l ≠ [] →
    List.foldr (fun p (tree : PBTree A) => impl.huffman.pbadd A p.1 tree p.2) (PBTree.pbleaf a)
        (List.map (fun p : A × List Bool => (p.1, false :: p.2)) l) =
      PBTree.pbleft
        (List.foldr (fun p (tree : PBTree A) => impl.huffman.pbadd A p.1 tree p.2) (PBTree.pbleaf a) l)

/-- Adding false-prefixed codes onto a right wrapper folds into a node. -/
def spec_fold_pbadd_prop_node (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A] (empty : A), ∀ (l : Code A) (a : PBTree A),
    l ≠ [] →
    List.foldr (fun p (tree : PBTree A) => impl.huffman.pbadd A p.1 tree p.2) (PBTree.pbright a)
        (List.map (fun p : A × List Bool => (p.1, false :: p.2)) l) =
      PBTree.pbnode
        (List.foldr (fun p (tree : PBTree A) => impl.huffman.pbadd A p.1 tree p.2) (PBTree.pbleaf empty) l)
        a

/-- Adding true-prefixed codes folds into a right wrapper. -/
def spec_fold_pbadd_prop_right (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A] (empty : A), ∀ (l : Code A) (a : A),
    l ≠ [] →
    List.foldr (fun p (tree : PBTree A) => impl.huffman.pbadd A p.1 tree p.2) (PBTree.pbleaf a)
        (List.map (fun p : A × List Bool => (p.1, true :: p.2)) l) =
      PBTree.pbright
        (List.foldr (fun p (tree : PBTree A) => impl.huffman.pbadd A p.1 tree p.2) (PBTree.pbleaf a) l)

/-- Every computed code entry corresponds to a leaf in the tree. -/
def spec_in_pbcompute_inpb (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A] (empty : A), ∀ (t : PBTree A) (a : A) (l : List Bool),
    (a, l) ∈ impl.huffman.compute_pbcode A t → inpb (PBTree.pbleaf a) t

/-- Adding into a leaf never creates a node as a subtree. -/
def spec_in_pbleaf_node (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A] (empty : A), ∀ (a1 a2 : PBTree A) (a3 a4 : A) (l : List Bool),
    ¬ inpb (PBTree.pbnode a1 a2) (impl.huffman.pbadd A a3 (PBTree.pbleaf a4) l)

/-- Every leaf in a tree has an associated computed code entry. -/
def spec_inpb_compute_ex (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A] (empty : A), ∀ (a : A) (p : PBTree A),
    inpb (PBTree.pbleaf a) p → ∃ l : List Bool, (a, l) ∈ impl.huffman.compute_pbcode A p

/-- Every partial binary tree contains a leaf. -/
def spec_inpb_ex (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A] (empty : A), ∀ t : PBTree A,
    ∃ x : A, inpb (PBTree.pbleaf x) t

/-- Adding a leaf makes that leaf a subtree of the result. -/
def spec_inpb_pbadd (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A] (empty : A), ∀ (a1 : A) (l1 : List Bool) (t1 : PBTree A),
    inpb (PBTree.pbleaf a1) (impl.huffman.pbadd A a1 t1 l1)

/-- Subtrees of an added tree are either the inserted leaf or old subtrees. -/
def spec_inpb_pbadd_ex (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A] (empty : A), ∀ (a1 : A) (l1 : List Bool) (t1 t : PBTree A),
    inpb t (impl.huffman.pbadd A a1 t1 l1) →
    inpb (PBTree.pbleaf a1) t ∨ inpb t t1

/-- Leaves in a built tree came from the source code. -/
def spec_inpb_pbbuild_inv (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A] (empty : A), ∀ (a : A) (c : Code A),
    c ≠ [] →
    inpb (PBTree.pbleaf a) (impl.huffman.pbbuild A empty c) →
    ∃ l : List Bool, (a, l) ∈ c

/-- Partial-binary subtree membership is transitive. -/
def spec_inpb_trans (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A] (empty : A), ∀ t1 t2 t3 : PBTree A,
    inpb t1 t2 → inpb t2 t3 → inpb t1 t3

/-- Adding into a leaf only leaves the inserted value. -/
def spec_inpbleaf_eq (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A] (empty : A), ∀ (a1 a2 a3 : A) (l : List Bool),
    inpb (PBTree.pbleaf a1) (impl.huffman.pbadd A a2 (PBTree.pbleaf a3) l) →
    a1 = a2

/-- Leaves in an added tree are either inserted or were already present. -/
def spec_inpbleaf_pbadd_inv (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A] (empty : A), ∀ (a1 a2 : A) (a3 : PBTree A) (l : List Bool),
    inpb (PBTree.pbleaf a1) (impl.huffman.pbadd A a2 a3 l) →
    a1 = a2 ∨ inpb (PBTree.pbleaf a1) a3

/-- A tree with distinct leaves has computed code with unique keys. -/
def spec_pb_unique_key (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A] (empty : A), ∀ t : PBTree A,
    distinct_pbleaves t → unique_key (impl.huffman.compute_pbcode A t)

/-- Prefix-related computed code entries identify the same leaf. -/
def spec_pb_unique_prefix1 (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A] (empty : A), ∀ (t : PBTree A) (a1 a2 : A) (lb1 lb2 : List Bool),
    (a1, lb1) ∈ impl.huffman.compute_pbcode A t →
    (a2, lb2) ∈ impl.huffman.compute_pbcode A t →
    is_prefix lb1 lb2 →
    a1 = a2

/-- A tree with distinct leaves has prefix-unique computed code. -/
def spec_pb_unique_prefix (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A] (empty : A), ∀ t : PBTree A,
    distinct_pbleaves t → unique_prefix (impl.huffman.compute_pbcode A t)

/-- Adding to a leaf computes to the singleton inserted code. -/
def spec_pbadd_prop1 (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A] (empty : A), ∀ (a1 a2 : A) (l1 : List Bool),
    impl.huffman.compute_pbcode A (impl.huffman.pbadd A a1 (PBTree.pbleaf a2) l1) = [(a1, l1)]

/-- Adding at a free position adds exactly one computed code entry. -/
def spec_pbadd_prop2 (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A] (empty : A), ∀ (a1 : A) (l1 : List Bool) (l2 : PBTree A),
    pbfree l1 l2 →
    List.Perm (impl.huffman.compute_pbcode A (impl.huffman.pbadd A a1 l2 l1))
      ((a1, l1) :: impl.huffman.compute_pbcode A l2)

/-- Building a tree from its computed code is identity for distinct leaves. -/
def spec_pbbuild_compute_peq (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A] (empty : A), ∀ t : PBTree A,
    distinct_pbleaves t →
    impl.huffman.pbbuild A empty (impl.huffman.compute_pbcode A t) = t

/-- Building then computing preserves a prefix-unique code up to permutation. -/
def spec_pbbuild_compute_perm (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A] (empty : A), ∀ c : Code A,
    c ≠ [] →
    unique_prefix c →
    List.Perm (impl.huffman.compute_pbcode A (impl.huffman.pbbuild A empty c)) c

/-- Building from a prefix-unique code creates a tree with distinct leaves. -/
def spec_pbbuild_distinct_pbleaves (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A] (empty : A), ∀ c : Code A,
    unique_prefix c → distinct_pbleaves (impl.huffman.pbbuild A empty c)

/-- Building from false-prefixed and true-prefixed nonempty codes creates a node. -/
def spec_pbbuild_pbnode (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A] (empty : A), ∀ c1 c2 : Code A,
    c1 ≠ [] →
    c2 ≠ [] →
    impl.huffman.pbbuild A empty
        (List.map (fun x : A × List Bool => (x.1, false :: x.2)) c1 ++
         List.map (fun x : A × List Bool => (x.1, true :: x.2)) c2) =
      PBTree.pbnode (impl.huffman.pbbuild A empty c1) (impl.huffman.pbbuild A empty c2)

/-- Building from true-prefixed code wraps the built tree on the right. -/
def spec_pbbuild_true_pbright (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A] (empty : A), ∀ c : Code A,
    c ≠ [] →
    impl.huffman.pbbuild A empty (List.map (fun x : A × List Bool => (x.1, true :: x.2)) c) =
      PBTree.pbright (impl.huffman.pbbuild A empty c)

/-- Non-prefix-related paths remain free after adding to a fresh leaf. -/
def spec_pbfree_pbadd_prop1 (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A] (empty : A), ∀ (a1 : A) (l l1 : List Bool),
    ¬ is_prefix l l1 →
    ¬ is_prefix l1 l →
    pbfree l (impl.huffman.pbadd A a1 (PBTree.pbleaf empty) l1)

/-- Free paths remain free after adding at an unrelated path. -/
def spec_pbfree_pbadd_prop2 (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A] (empty : A), ∀ (a : A) (l1 l2 : List Bool) (l3 : PBTree A),
    pbfree l1 l3 →
    ¬ is_prefix l2 l1 →
    ¬ is_prefix l1 l2 →
    pbfree l1 (impl.huffman.pbadd A a l3 l2)

/-- In a prefix-unique code, another code's tree leaves a conflicting path free. -/
def spec_pbfree_pbbuild_prop1 (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A] (empty : A), ∀ (a : A) (l1 : List Bool) (l2 : Code A),
    l2 ≠ [] →
    unique_prefix ((a, l1) :: l2) →
    pbfree l1 (impl.huffman.pbbuild A empty l2)

/-- Every partial binary tree is either a leaf or not equal to any leaf. -/
def spec_pbleaf_or_not (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A] (empty : A), ∀ p : PBTree A,
    (∃ a : A, p = PBTree.pbleaf a) ∨ (∀ a : A, p ≠ PBTree.pbleaf a)
