import Huffman.Harness
import Huffman.Impl.Prod2List

/-!
# Huffman.Spec.Prod2List

Frozen specifications translated from Coq's `Prod2List.v`.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- Coq theorem `prod2list_app` translated as a proof obligation. -/
def spec_prod2list_app (impl : RepoImpl) : Prop :=
  ∀ (A : Type) (f : A → Nat),
    ∀ (l1 l3 : List Nat) (l2 l4 : List (BTree A)),
      List.length l1 = List.length l2 →
        impl.huffman.prod2list A f (l1 ++ l3) (l2 ++ l4) =
          impl.huffman.prod2list A f l1 l2 + impl.huffman.prod2list A f l3 l4

/-- Coq theorem `prod2list_eq` translated as a proof obligation. -/
def spec_prod2list_eq (impl : RepoImpl) : Prop :=
  ∀ (A : Type) (f : A → Nat),
    ∀ (a : Nat) (b c : BTree A)
      (l1 l2 l3 : List Nat) (l4 l5 l6 : List (BTree A)),
      List.length l1 = List.length l4 →
        List.length l2 = List.length l5 →
          List.length l3 = List.length l6 →
            impl.huffman.prod2list A f (l1 ++ a :: l2 ++ a :: l3) (l4 ++ b :: l5 ++ c :: l6) =
              impl.huffman.prod2list A f (l1 ++ a :: l2 ++ a :: l3) (l4 ++ c :: l5 ++ b :: l6)

/-- Coq theorem `prod2list_le_l` translated as a proof obligation. -/
def spec_prod2list_le_l (impl : RepoImpl) : Prop :=
  ∀ (A : Type) (f : A → Nat),
    ∀ (a b : Nat) (c d : BTree A)
      (l1 l2 l3 : List Nat) (l4 l5 l6 : List (BTree A)),
      List.length l1 = List.length l4 →
        List.length l2 = List.length l5 →
          List.length l3 = List.length l6 →
            impl.huffman.sum_leaves A f c ≤ impl.huffman.sum_leaves A f d →
              a ≤ b →
                impl.huffman.prod2list A f (l1 ++ a :: l2 ++ b :: l3) (l4 ++ d :: l5 ++ c :: l6) ≤
                  impl.huffman.prod2list A f (l1 ++ a :: l2 ++ b :: l3) (l4 ++ c :: l5 ++ d :: l6)

/-- Coq theorem `prod2list_le_r` translated as a proof obligation. -/
def spec_prod2list_le_r (impl : RepoImpl) : Prop :=
  ∀ (A : Type) (f : A → Nat),
    ∀ (a b : Nat) (c d : BTree A)
      (l1 l2 l3 : List Nat) (l4 l5 l6 : List (BTree A)),
      List.length l1 = List.length l4 →
        List.length l2 = List.length l5 →
          List.length l3 = List.length l6 →
            impl.huffman.sum_leaves A f d ≤ impl.huffman.sum_leaves A f c →
              b ≤ a →
                impl.huffman.prod2list A f (l1 ++ a :: l2 ++ b :: l3) (l4 ++ d :: l5 ++ c :: l6) ≤
                  impl.huffman.prod2list A f (l1 ++ a :: l2 ++ b :: l3) (l4 ++ c :: l5 ++ d :: l6)

/-- Coq theorem `prod2list_reorder2` translated as a proof obligation. -/
def spec_prod2list_reorder2 (impl : RepoImpl) : Prop :=
  ∀ (A : Type) (f : A → Nat),
    ∀ (a : Nat) (b c b1 c1 : BTree A)
      (l1 l2 : List Nat) (l3 l4 l5 : List (BTree A)),
      List.length l1 = List.length l3 →
        List.length l2 = List.length l4 →
          (∀ n : Nat, n ∈ l1 → n ≤ a) →
            (∀ n : Nat, n ∈ l2 → n ≤ a) →
              List.Perm (l3 ++ b :: c :: l4) (b1 :: c1 :: l5) →
                ordered (sum_order f) (b1 :: c1 :: l5) →
                  ∃ l6 : List (BTree A),
                    ∃ l7 : List (BTree A),
                      List.length l1 = List.length l6 ∧
                        List.length l2 = List.length l7 ∧
                          List.Perm (b1 :: c1 :: l5) (l6 ++ b1 :: c1 :: l7) ∧
                            impl.huffman.prod2list A f (l1 ++ a :: a :: l2) (l6 ++ b1 :: c1 :: l7) ≤
                              impl.huffman.prod2list A f (l1 ++ a :: a :: l2) (l3 ++ b :: c :: l4)

/-- Coq theorem `prod2list_reorder` translated as a proof obligation. -/
def spec_prod2list_reorder (impl : RepoImpl) : Prop :=
  ∀ (A : Type) (f : A → Nat),
    ∀ (a : Nat) (b b1 : BTree A)
      (l1 l2 : List Nat) (l3 l4 l5 : List (BTree A)),
      List.length l1 = List.length l3 →
        List.length l2 = List.length l4 →
          (∀ n : Nat, n ∈ l1 → n ≤ a) →
            (∀ n : Nat, n ∈ l2 → n ≤ a) →
              List.Perm (l3 ++ b :: l4) (b1 :: l5) →
                ordered (sum_order f) (b1 :: l5) →
                  ∃ l6 : List (BTree A),
                    ∃ l7 : List (BTree A),
                      List.length l1 = List.length l6 ∧
                        List.length l2 = List.length l7 ∧
                          List.Perm (b1 :: l5) (l6 ++ b1 :: l7) ∧
                            impl.huffman.prod2list A f (l1 ++ a :: l2) (l6 ++ b1 :: l7) ≤
                              impl.huffman.prod2list A f (l1 ++ a :: l2) (l3 ++ b :: l4)
