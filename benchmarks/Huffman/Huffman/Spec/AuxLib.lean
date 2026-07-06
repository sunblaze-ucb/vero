import Huffman.Harness
import Huffman.Impl.AuxLib

/-!
# Huffman.Spec.AuxLib

Frozen specifications translated from Coq's `AuxLib.v`.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- Coq theorem `NoDup_app` translated as a proof obligation. -/
def spec_NoDup_app (impl : RepoImpl) : Prop :=
  ∀ (A B C : Type), ∀ (l1 l2 : List A),
    List.Nodup l1 → List.Nodup l2 →
    (∀ a : A, a ∈ l1 → a ∈ l2 → False) →
    List.Nodup (l1 ++ l2)

/-- Coq theorem `NoDup_app_inv` translated as a proof obligation. -/
def spec_NoDup_app_inv (impl : RepoImpl) : Prop :=
  ∀ (A B C : Type), ∀ (l1 l2 : List A) (a : A),
    List.Nodup (l1 ++ l2) → a ∈ l1 → a ∈ l2 → False

/-- Coq theorem `NoDup_app_inv_l` translated as a proof obligation. -/
def spec_NoDup_app_inv_l (impl : RepoImpl) : Prop :=
  ∀ (A B C : Type), ∀ (l1 l2 : List A),
    List.Nodup (l1 ++ l2) → List.Nodup l1

/-- Coq theorem `NoDup_app_inv_r` translated as a proof obligation. -/
def spec_NoDup_app_inv_r (impl : RepoImpl) : Prop :=
  ∀ (A B C : Type), ∀ (l1 l2 : List A),
    List.Nodup (l1 ++ l2) → List.Nodup l2

/-- Coq theorem `Permutation_transposition` translated as a proof obligation. -/
def spec_Permutation_transposition (impl : RepoImpl) : Prop :=
  ∀ (A B C : Type), ∀ (a b : A) (l1 l2 : List A),
    List.Perm (a :: l1 ++ b :: l2) (b :: l1 ++ a :: l2)

/-- Coq theorem `all_permutations_aux_permutation` translated as a proof obligation. -/
def spec_all_permutations_aux_permutation (impl : RepoImpl) : Prop :=
  ∀ (A B C : Type), ∀ (n : Nat) (l1 l2 : List A),
    n = List.length l2 → l1 ∈ all_permutations_aux l2 n → List.Perm l1 l2

/-- Coq theorem `all_permutations_permutation` translated as a proof obligation. -/
def spec_all_permutations_permutation (impl : RepoImpl) : Prop :=
  ∀ (A B C : Type), ∀ (l1 l2 : List A),
    l1 ∈ all_permutations l2 → List.Perm l1 l2

/-- Coq theorem `app_inv_app2` translated as a proof obligation. -/
def spec_app_inv_app2 (impl : RepoImpl) : Prop :=
  ∀ (A B C : Type), ∀ (l1 l2 l3 l4 : List A) (a b : A),
    l1 ++ l2 = l3 ++ a :: b :: l4 →
    (∃ l5 : List A, l1 = l3 ++ a :: b :: l5) ∨
      (∃ l5 : List A, l2 = l5 ++ a :: b :: l4) ∨
      l1 = l3 ++ a :: [] ∧ l2 = b :: l4

/-- Coq theorem `app_inv_app` translated as a proof obligation. -/
def spec_app_inv_app (impl : RepoImpl) : Prop :=
  ∀ (A B C : Type), ∀ (l1 l2 l3 l4 : List A) (a : A),
    l1 ++ l2 = l3 ++ a :: l4 →
    (∃ l5 : List A, l1 = l3 ++ a :: l5) ∨
      (∃ l5 : List A, l2 = l5 ++ a :: l4)

/-- Coq theorem `exist_first_max` translated as a proof obligation. -/
def spec_exist_first_max (impl : RepoImpl) : Prop :=
  ∀ (A B C : Type), ∀ l : List Nat,
    l ≠ [] →
    ∃ a : Nat,
      ∃ l1 : List Nat,
        ∃ l2 : List Nat,
          l = l1 ++ a :: l2 ∧
            (∀ n1, n1 ∈ l1 → n1 < a) ∧
            (∀ n1, n1 ∈ l2 → n1 ≤ a)

/-- Coq theorem `find_max_correct` translated as a proof obligation. -/
def spec_find_max_correct (impl : RepoImpl) : Prop :=
  ∀ (A B C : Type), ∀ (f : A → Nat) (l : List A),
    match find_max f l with
    | none => l = []
    | some (a, b) => (b ∈ l ∧ a = f b) ∧ (∀ c : A, c ∈ l → f c ≤ f b)

/-- Coq theorem `find_min_correct` translated as a proof obligation. -/
def spec_find_min_correct (impl : RepoImpl) : Prop :=
  ∀ (A B C : Type), ∀ (f : A → Nat) (l : List A),
    match find_min f l with
    | none => l = []
    | some (a, b) => (b ∈ l ∧ a = f b) ∧ (∀ c : A, c ∈ l → f b ≤ f c)

/-- Coq theorem `firstn_le_app1` translated as a proof obligation. -/
def spec_firstn_le_app1 (impl : RepoImpl) : Prop :=
  ∀ (A B C : Type), ∀ (n : Nat) (l1 l2 : List A),
    List.length l1 ≤ n →
    List.take n (l1 ++ l2) = l1 ++ List.take (n - List.length l1) l2

/-- Coq theorem `firstn_le_app2` translated as a proof obligation. -/
def spec_firstn_le_app2 (impl : RepoImpl) : Prop :=
  ∀ (A B C : Type), ∀ (n : Nat) (l1 l2 : List A),
    n ≤ List.length l1 → List.take n (l1 ++ l2) = List.take n l1

/-- Coq theorem `firstn_le_length_eq` translated as a proof obligation. -/
def spec_firstn_le_length_eq (impl : RepoImpl) : Prop :=
  ∀ (A B C : Type), ∀ (n : Nat) (l1 : List A),
    n ≤ List.length l1 → List.length (List.take n l1) = n

/-- Coq theorem `fold_left_eta` translated as a proof obligation. -/
def spec_fold_left_eta (impl : RepoImpl) : Prop :=
  ∀ (A B C : Type), ∀ (l : List B) (a : A) (f f1 : A → B → A),
    (∀ (x : A) (b : B), b ∈ l → f x b = f1 x b) →
    List.foldl f a l = List.foldl f1 a l

/-- Coq theorem `fold_left_init` translated as a proof obligation. -/
def spec_fold_left_init (impl : RepoImpl) : Prop :=
  ∀ (A B C : Type), ∀ (f : A → B → A) (h : A → A),
    (∀ (a : A) (b : B), h (f a b) = f (h a) b) →
    ∀ (a : A) (l : List B), List.foldl f (h a) l = h (List.foldl f a l)

/-- Coq theorem `fold_left_map` translated as a proof obligation. -/
def spec_fold_left_map (impl : RepoImpl) : Prop :=
  ∀ (A B C D : Type), ∀ (f : A → B → A) (a : A) (l : List D) (k : D → B),
    List.foldl f a (List.map k l) = List.foldl (fun x y => f x (k y)) a l

/-- Coq theorem `fold_left_permutation` translated as a proof obligation. -/
def spec_fold_left_permutation (impl : RepoImpl) : Prop :=
  ∀ (A B C : Type), ∀ (D E : Type) (f : D → E → D),
    (∀ (a : D) (b1 b2 : E), f (f a b1) b2 = f (f a b2) b1) →
    ∀ (a : D) (l1 l2 : List E), List.Perm l1 l2 → List.foldl f a l1 = List.foldl f a l2

/-- Coq theorem `in_flat_map_ex` translated as a proof obligation. -/
def spec_in_flat_map_ex (impl : RepoImpl) : Prop :=
  ∀ (A B C : Type), ∀ (l : List B) (f : B → List C) (a : C),
    a ∈ List.flatMap f l → ∃ b : B, b ∈ l ∧ a ∈ f b

/-- Coq theorem `in_flat_map_in` translated as a proof obligation. -/
def spec_in_flat_map_in (impl : RepoImpl) : Prop :=
  ∀ (A B C : Type), ∀ (l : List B) (f : B → List C) (a : C) (b : B),
    a ∈ f b → b ∈ l → a ∈ List.flatMap f l

/-- Coq theorem `in_map_fst_inv` translated as a proof obligation. -/
def spec_in_map_fst_inv (impl : RepoImpl) : Prop :=
  ∀ (A B C : Type), ∀ (a : B) (l : List (B × C)),
    a ∈ List.map Prod.fst l → ∃ c : C, (a, c) ∈ l

/-- Coq theorem `map2_app` translated as a proof obligation. -/
def spec_map2_app (impl : RepoImpl) : Prop :=
  ∀ (A B C : Type), ∀ (f : A → B → C) (l1 l3 : List A) (l2 l4 : List B),
    List.length l1 = List.length l2 →
    map2 f (l1 ++ l3) (l2 ++ l4) = map2 f l1 l2 ++ map2 f l3 l4

/-- Coq theorem `permutation_all_permutations` translated as a proof obligation. -/
def spec_permutation_all_permutations (impl : RepoImpl) : Prop :=
  ∀ (A B C : Type), ∀ (l1 l2 : List A),
    List.Perm l1 l2 → l1 ∈ all_permutations l2

/-- Coq theorem `same_length_ex` translated as a proof obligation. -/
def spec_same_length_ex (impl : RepoImpl) : Prop :=
  ∀ (A B C : Type), ∀ (a : A) (l1 l2 : List A) (l3 : List B),
    List.length (l1 ++ a :: l2) = List.length l3 →
    ∃ l4 : List B,
      ∃ l5 : List B,
        ∃ b : B,
          List.length l1 = List.length l4 ∧
            List.length l2 = List.length l5 ∧
            l3 = l4 ++ b :: l5

/-- Coq theorem `skipn_le_app1` translated as a proof obligation. -/
def spec_skipn_le_app1 (impl : RepoImpl) : Prop :=
  ∀ (A B C : Type), ∀ (n : Nat) (l1 l2 : List A),
    List.length l1 ≤ n → List.drop n (l1 ++ l2) = List.drop (n - List.length l1) l2

/-- Coq theorem `skipn_le_app2` translated as a proof obligation. -/
def spec_skipn_le_app2 (impl : RepoImpl) : Prop :=
  ∀ (A B C : Type), ∀ (n : Nat) (l1 l2 : List A),
    n ≤ List.length l1 → List.drop n (l1 ++ l2) = List.drop n l1 ++ l2

/-- Coq theorem `split_one_in_ex` translated as a proof obligation. -/
def spec_split_one_in_ex (impl : RepoImpl) : Prop :=
  ∀ (A B C : Type), ∀ (a : A) (l1 : List A),
    a ∈ l1 → ∃ l2 : List A, (a, l2) ∈ split_one l1

/-- Coq theorem `split_one_permutation` translated as a proof obligation. -/
def spec_split_one_permutation (impl : RepoImpl) : Prop :=
  ∀ (A B C : Type), ∀ (a : A) (l1 l2 : List A),
    (a, l1) ∈ split_one l2 → List.Perm (a :: l1) l2
