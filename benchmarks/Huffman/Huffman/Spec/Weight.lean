import Huffman.Harness
import Huffman.Impl.Weight

/-!
# Huffman.Spec.Weight

Frozen specifications translated from Coq's `Weight.v`.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- Coq theorem `NoDup_unique_key` translated as a proof obligation. -/
def spec_weight_NoDup_unique_key (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A], ∀ (B C : Type) (l : List (B × C)),
    List.Nodup (List.map Prod.fst l) → unique_key l

/-- Coq theorem `fold_plus_permutation` translated as a proof obligation. -/
def spec_fold_plus_permutation (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A], ∀ (B : Type) (l1 l2 : List B) (c : Nat) (f : B → Nat),
    List.Perm l1 l2 →
      List.foldl (fun (a : Nat) (b : B) => a + f b) c l1 =
        List.foldl (fun (a : Nat) (b : B) => a + f b) c l2

/-- Coq theorem `fold_plus_split` translated as a proof obligation. -/
def spec_fold_plus_split (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A], ∀ (B : Type) (l : List B) (c : Nat) (f : B → Nat),
    c + List.foldl (fun (a : Nat) (b : B) => a + f b) 0 l =
      List.foldl (fun (a : Nat) (b : B) => a + f b) c l

/-- Coq theorem `frequency_length` translated as a proof obligation. -/
def spec_frequency_length (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A], ∀ (m : List A) (c : Code A),
    unique_key c →
      List.length (impl.huffman.encode A c m) =
        List.foldl
          (fun a b =>
            a + impl.huffman.number_of_occurrences A (Prod.fst b) m *
              List.length (Prod.snd b))
          0
          c

/-- Coq theorem `length_encode_nId` translated as a proof obligation. -/
def spec_length_encode_nId (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A], ∀ (a : A) (l1 : List Bool) (l : Code A) (n : Nat),
    List.length (impl.huffman.encode A ((a, l1) :: l) (id_list a n)) =
      n * List.length l1

/-- Coq theorem `restrict_code_encode_length` translated as a proof obligation. -/
def spec_restrict_code_encode_length (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A], ∀ (m : List A) (c : Code A),
    impl.huffman.encode A c m =
      impl.huffman.encode A (impl.huffman.weight_restrict_code A m c) m

/-- Coq theorem `restrict_code_encode_length_inc` translated as a proof obligation. -/
def spec_restrict_code_encode_length_inc (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A], ∀ (m m1 : List A) (c : Code A),
    (∀ a : A, a ∈ m1 → a ∈ m) →
      impl.huffman.encode A c m1 =
        impl.huffman.encode A (impl.huffman.weight_restrict_code A m c) m1

/-- Coq theorem `restrict_code_in` translated as a proof obligation. -/
def spec_weight_restrict_code_in (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A], ∀ (m : List A) (a : A) (c : Code A),
    a ∈ m →
      impl.huffman.find_code A a c =
        impl.huffman.find_code A a (impl.huffman.weight_restrict_code A m c)

/-- Coq theorem `restrict_code_unique_key` translated as a proof obligation. -/
def spec_weight_restrict_code_unique_key (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A], ∀ (m : List A) (c : Code A),
    unique_key (impl.huffman.weight_restrict_code A m c)

/-- Coq theorem `weight_permutation` translated as a proof obligation. -/
def spec_weight_permutation (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A], ∀ (m : List A) (c1 c2 : Code A),
    unique_prefix c1 →
      List.Perm c1 c2 →
        impl.huffman.weight A m c1 = impl.huffman.weight A m c2

/-- `weight` is additive over message concatenation: encoding `m1 ++ m2` costs
    exactly the sum of the two parts' encoded costs. Anchors `weight` to a
    length-like additive measure over the message rather than an arbitrary value. -/
def spec_weight_append_additive (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A], ∀ (m1 m2 : List A) (c : Code A),
    impl.huffman.weight A (m1 ++ m2) c =
      impl.huffman.weight A m1 c + impl.huffman.weight A m2 c

/-- Appending a symbol with a nonempty codeword strictly increases the encoded
    weight. Together with additivity this pins `weight` to genuinely count the
    encoded bits: a constant weight (e.g. `weight ≡ 0`) fails the strict `<`, and
    the codeword is reached through `find_code` (itself pinned by
    `spec_find_code_correct2`), so it cannot be dodged by a degenerate stub. -/
def spec_weight_append_grows (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A], ∀ (m : List A) (a : A) (c : Code A),
    impl.huffman.find_code A a c ≠ [] →
      impl.huffman.weight A m c < impl.huffman.weight A (m ++ [a]) c
