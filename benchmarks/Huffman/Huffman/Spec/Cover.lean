import Huffman.Harness
import Huffman.Impl.Cover

/-!
# Huffman.Spec.Cover

Frozen specifications translated from Coq's `Cover.v`.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- Coq theorem `all_cover_aux_cover` translated as a proof obligation. -/
def spec_all_cover_aux_cover (impl : RepoImpl) : Prop :=
  ∀ (A : Type), ∀ (n : Nat) (l : List (BTree A)) (t : BTree A),
    n = List.length l → t ∈ all_cover_aux l n → cover l t

/-- Coq theorem `all_cover_cover` translated as a proof obligation. -/
def spec_all_cover_cover (impl : RepoImpl) : Prop :=
  ∀ (A : Type), ∀ (l : List (BTree A)) (t : BTree A), t ∈ all_cover l → cover l t

/-- Coq theorem `cover_all_cover` translated as a proof obligation. -/
def spec_cover_all_cover (impl : RepoImpl) : Prop :=
  ∀ (A : Type), ∀ (l : List (BTree A)) (t : BTree A), cover l t → t ∈ all_cover l

/-- Coq theorem `cover_all_leaves` translated as a proof obligation. -/
def spec_cover_all_leaves (impl : RepoImpl) : Prop :=
  ∀ (A : Type), ∀ t : BTree A,
    cover (List.map (fun x : A => BTree.leaf x) (impl.huffman.all_leaves A t)) t

/-- Coq theorem `cover_app` translated as a proof obligation. -/
def spec_cover_app (impl : RepoImpl) : Prop :=
  ∀ (A : Type), ∀ (t1 t2 : BTree A) (l1 l2 : List (BTree A)),
    cover l1 t1 → cover l2 t2 → cover (l1 ++ l2) (BTree.node t1 t2)

/-- Coq theorem `cover_cons_l` translated as a proof obligation. -/
def spec_cover_cons_l (impl : RepoImpl) : Prop :=
  ∀ (A : Type), ∀ (t1 t2 : BTree A) (l1 : List (BTree A)),
    cover l1 t1 → cover (t2 :: l1) (BTree.node t2 t1)

/-- Coq theorem `cover_in_inb` translated as a proof obligation. -/
def spec_cover_in_inb (impl : RepoImpl) : Prop :=
  ∀ (A : Type), ∀ (l : List (BTree A)) (t1 t2 : BTree A),
    cover l t1 → t2 ∈ l → inb t2 t1

/-- Coq theorem `cover_in_inb_inb` translated as a proof obligation. -/
def spec_cover_in_inb_inb (impl : RepoImpl) : Prop :=
  ∀ (A : Type), ∀ (l : List (BTree A)) (t1 t2 t3 : BTree A),
    cover l t1 → t2 ∈ l → inb t3 t2 → inb t3 t1

/-- Coq theorem `cover_inv_app` translated as a proof obligation. -/
def spec_cover_inv_app (impl : RepoImpl) : Prop :=
  ∀ (A : Type), ∀ (t1 t2 : BTree A) (l : List (BTree A)),
    cover l (BTree.node t1 t2) →
    l = BTree.node t1 t2 :: [] ∨
      (∃ l1 : List (BTree A),
        ∃ l2 : List (BTree A),
          (cover l1 t1 ∧ cover l2 t2) ∧ List.Perm l (l1 ++ l2))

/-- Coq theorem `cover_inv_leaf` translated as a proof obligation. -/
def spec_cover_inv_leaf (impl : RepoImpl) : Prop :=
  ∀ (A : Type), ∀ (a : A) (l : List (BTree A)),
    cover l (BTree.leaf a) → l = BTree.leaf a :: []

/-- Coq theorem `cover_not_nil` translated as a proof obligation. -/
def spec_cover_not_nil (impl : RepoImpl) : Prop :=
  ∀ (A : Type), ∀ (l : List (BTree A)) (t : BTree A), cover l t → l ≠ []

/-- Coq theorem `cover_number_of_nodes` translated as a proof obligation. -/
def spec_cover_number_of_nodes (impl : RepoImpl) : Prop :=
  ∀ (A : Type), ∀ (t : BTree A) (l : List (BTree A)),
    cover l t →
    number_of_nodes t =
      List.foldl (fun x y => x + number_of_nodes y) 0 l + Nat.pred (List.length l)

/-- Coq theorem `cover_one_inv` translated as a proof obligation. -/
def spec_cover_one_inv (impl : RepoImpl) : Prop :=
  ∀ (A : Type), ∀ t1 t2 : BTree A, cover (t1 :: []) t2 → t1 = t2

/-- Coq theorem `cover_permutation` translated as a proof obligation. -/
def spec_cover_permutation (impl : RepoImpl) : Prop :=
  ∀ (A : Type), ∀ (t : BTree A) (l1 l2 : List (BTree A)),
    cover l1 t → List.Perm l1 l2 → cover l2 t

/-- Coq theorem `one_cover_ex` translated as a proof obligation. -/
def spec_one_cover_ex (impl : RepoImpl) : Prop :=
  ∀ (A : Type), ∀ l : List (BTree A), l ≠ [] → ∃ t : BTree A, cover l t
