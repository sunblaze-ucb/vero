import Huffman.Harness
import Huffman.Impl.Frequency

/-!
# Huffman.Spec.Frequency

Frozen specifications translated from Coq's `Frequency.v`.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- Coq theorem `add_frequency_list_1` translated as a proof obligation. -/
def spec_add_frequency_list_1 (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A], ∀ a l,
    (∀ ca, ¬ (a, ca) ∈ l) →
      (a, 1) ∈ impl.huffman.add_frequency_list A a l

/-- Coq theorem `add_frequency_list_in` translated as a proof obligation. -/
def spec_add_frequency_list_in (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A], ∀ m a n,
    unique_key m →
      (a, n) ∈ m →
        (a, n + 1) ∈ impl.huffman.add_frequency_list A a m

/-- Coq theorem `add_frequency_list_in_inv` translated as a proof obligation. -/
def spec_add_frequency_list_in_inv (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A], ∀ (a1 a2 : A) (b1 : Nat) l,
    (a1, b1) ∈ impl.huffman.add_frequency_list A a2 l →
      a1 = a2 ∨ (a1, b1) ∈ l

/-- Coq theorem `add_frequency_list_not_in` translated as a proof obligation. -/
def spec_add_frequency_list_not_in (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A], ∀ m a b n,
    a ≠ b →
      (a, n) ∈ m →
        (a, n) ∈ impl.huffman.add_frequency_list A b m

/-- Coq theorem `add_frequency_list_perm` translated as a proof obligation. -/
def spec_add_frequency_list_perm (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A], ∀ (a : A) l,
    List.Perm
      (a :: List.flatMap (fun p : A × Nat => id_list (Prod.fst p) (Prod.snd p)) l)
      (List.flatMap (fun p : A × Nat => id_list (Prod.fst p) (Prod.snd p))
        (impl.huffman.add_frequency_list A a l))

/-- Coq theorem `add_frequency_list_unique_key` translated as a proof obligation. -/
def spec_add_frequency_list_unique_key (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A], ∀ (a : A) l,
    unique_key l →
      unique_key (impl.huffman.add_frequency_list A a l)

/-- Coq theorem `frequency_list_in` translated as a proof obligation. -/
def spec_frequency_list_in (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A], ∀ a n m,
    (a, n) ∈ impl.huffman.frequency_list A m →
      a ∈ m

/-- Coq theorem `frequency_list_perm` translated as a proof obligation. -/
def spec_frequency_list_perm (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A], ∀ l : List A,
    List.Perm l
      (List.flatMap (fun p : A × Nat => id_list (Prod.fst p) (Prod.snd p))
        (impl.huffman.frequency_list A l))

/-- Coq theorem `frequency_list_unique` translated as a proof obligation. -/
def spec_frequency_list_unique (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A], ∀ l : List A,
    unique_key (impl.huffman.frequency_list A l)

/-- Coq theorem `frequency_number_of_occurrences` translated as a proof obligation. -/
def spec_frequency_number_of_occurrences (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A], ∀ a m,
    a ∈ m →
      (a, impl.huffman.number_of_occurrences A a m) ∈ impl.huffman.frequency_list A m

/-- Coq theorem `in_frequency_map` translated as a proof obligation. -/
def spec_in_frequency_map (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A], ∀ l a,
    a ∈ l →
      a ∈ List.map Prod.fst (impl.huffman.frequency_list A l)

/-- Coq theorem `in_frequency_map_inv` translated as a proof obligation. -/
def spec_in_frequency_map_inv (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A], ∀ l a,
    a ∈ List.map Prod.fst (impl.huffman.frequency_list A l) →
      a ∈ l

/-- Coq theorem `number_of_occurrences_O` translated as a proof obligation. -/
def spec_number_of_occurrences_O (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A], ∀ a l,
    ¬ a ∈ l →
      impl.huffman.number_of_occurrences A a l = 0

/-- Coq theorem `number_of_occurrences_app` translated as a proof obligation. -/
def spec_number_of_occurrences_app (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A], ∀ l1 l2 a,
    impl.huffman.number_of_occurrences A a (l1 ++ l2) =
      impl.huffman.number_of_occurrences A a l1 +
        impl.huffman.number_of_occurrences A a l2

/-- Coq theorem `number_of_occurrences_permutation` translated as a proof obligation. -/
def spec_number_of_occurrences_permutation (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A], ∀ l1 l2 a,
    List.Perm l1 l2 →
      impl.huffman.number_of_occurrences A a l1 =
        impl.huffman.number_of_occurrences A a l2

/-- Coq theorem `number_of_occurrences_permutation_ex` translated as a proof obligation. -/
def spec_number_of_occurrences_permutation_ex (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A], ∀ (m : List A) (a : A),
    ∃ m1 : List A,
      List.Perm m (id_list a (impl.huffman.number_of_occurrences A a m) ++ m1) ∧
        ¬ a ∈ m1
