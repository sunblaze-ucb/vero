import Huffman.Harness
import Huffman.Impl.Code
import Huffman.Impl.Frequency

/-!
# Huffman.Spec.Code

Frozen specifications translated from Coq's `Code.v`. Each `spec_*` is a
property over an arbitrary `impl : RepoImpl`.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- Coq theorem `correct_encoding` translated as a proof obligation. -/
def spec_correct_encoding (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A], ∀ c : Code A, unique_prefix c → not_null c → ∀ m : List A,
    in_alphabet m c → impl.huffman.decode A c (impl.huffman.encode A c m) = m

/-- Coq theorem `decode_aux_correct` translated as a proof obligation. -/
def spec_decode_aux_correct (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A], ∀ c : Code A, unique_prefix c → not_null c →
    ∀ (m1 m2 head : List Bool) (a : A),
      impl.huffman.find_val A (head ++ m1) c = some a →
      decode_aux c head (m1 ++ m2) = a :: decode_aux c [] m2

/-- Coq theorem `decode_correct` translated as a proof obligation. -/
def spec_decode_correct (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A], ∀ c : Code A, unique_prefix c → not_null c →
    ∀ (m1 m2 : List Bool) (a : A),
      impl.huffman.find_val A m1 c = some a →
      impl.huffman.decode A c (m1 ++ m2) = a :: impl.huffman.decode A c m2

/-- Coq theorem `encode_app` translated as a proof obligation. -/
def spec_encode_app (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A], ∀ (l1 l2 : List A) (c : Code A),
    impl.huffman.encode A c (l1 ++ l2) = impl.huffman.encode A c l1 ++ impl.huffman.encode A c l2

/-- Coq theorem `encode_cons_inv` translated as a proof obligation. -/
def spec_encode_cons_inv (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A], ∀ (a : A) (l1 : List Bool) (l : Code A) (m1 : List A),
    a ∉ m1 → impl.huffman.encode A ((a, l1) :: l) m1 = impl.huffman.encode A l m1

/-- Coq theorem `encode_permutation` translated as a proof obligation. -/
def spec_encode_permutation (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A], ∀ (m : List A) (c1 c2 : Code A),
    List.Perm c1 c2 → unique_prefix c1 → impl.huffman.encode A c1 m = impl.huffman.encode A c2 m

/-- Coq theorem `encode_permutation_val` translated as a proof obligation. -/
def spec_encode_permutation_val (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A], ∀ (m1 m2 : List A) (c : Code A),
    List.Perm m1 m2 → List.Perm (impl.huffman.encode A c m1) (impl.huffman.encode A c m2)

/-- Coq theorem `find_code_app` translated as a proof obligation. -/
def spec_find_code_app (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A], ∀ (a : A) (l1 l2 : Code A),
    not_null l1 →
    impl.huffman.find_code A a (l1 ++ l2) =
      match impl.huffman.find_code A a l1 with
      | [] => impl.huffman.find_code A a l2
      | b1 :: l3 => b1 :: l3

/-- Coq theorem `find_code_correct1` translated as a proof obligation. -/
def spec_find_code_correct1 (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A], ∀ (c : Code A) (a : A) (b : Bool) (l : List Bool),
    impl.huffman.find_code A a c = b :: l → (a, b :: l) ∈ c

/-- Coq theorem `find_code_correct2` translated as a proof obligation. -/
def spec_find_code_correct2 (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A], ∀ (c : Code A) (a : A) (l : List Bool),
    unique_key c → (a, l) ∈ c → impl.huffman.find_code A a c = l

/-- Coq theorem `find_code_permutation` translated as a proof obligation. -/
def spec_find_code_permutation (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A], ∀ (a : A) (c1 c2 : Code A),
    List.Perm c1 c2 → unique_prefix c1 → impl.huffman.find_code A a c1 = impl.huffman.find_code A a c2

/-- Coq theorem `find_val_correct1` translated as a proof obligation. -/
def spec_find_val_correct1 (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A], ∀ (c : Code A) (a : A) (l : List Bool),
    impl.huffman.find_val A l c = some a → (a, l) ∈ c

/-- Coq theorem `find_val_correct2` translated as a proof obligation. -/
def spec_find_val_correct2 (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A], ∀ (c : Code A) (a : A) (l : List Bool),
    unique_prefix c → (a, l) ∈ c → impl.huffman.find_val A l c = some a

/-- Coq theorem `frequency_not_null` translated as a proof obligation. -/
def spec_frequency_not_null (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A], ∀ (m : List A) (c : Code A),
    1 < List.length (impl.huffman.frequency_list A m) →
    unique_prefix c → in_alphabet m c → not_null c

/-- Coq theorem `in_alphabet_cons` translated as a proof obligation. -/
def spec_in_alphabet_cons (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A], ∀ (m : List A) (c : Code A) (a : A) (ca : List Bool),
    (a, ca) ∈ c → in_alphabet m c → in_alphabet (a :: m) c

/-- Coq theorem `in_alphabet_incl` translated as a proof obligation. -/
def spec_in_alphabet_incl (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A], ∀ (m1 m2 : List A) (c : Code A),
    (∀ a : A, a ∈ m1 → a ∈ m2) → in_alphabet m2 c → in_alphabet m1 c

/-- Coq theorem `in_alphabet_inv` translated as a proof obligation. -/
def spec_in_alphabet_inv (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A], ∀ (c : Code A) (a : A) (l : List A),
    in_alphabet (a :: l) c → in_alphabet l c

/-- Coq theorem `in_alphabet_nil` translated as a proof obligation. -/
def spec_in_alphabet_nil (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A], ∀ c : Code A, in_alphabet [] c

/-- Coq theorem `in_find_map` translated as a proof obligation. -/
def spec_in_find_map (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A], ∀ (p : Code A) (a : A) (l : List Bool) (b : Bool),
    (a, l) ∈ p →
    impl.huffman.find_code A a
      (List.map (fun v : A × List Bool => match v with | (a1, b1) => (a1, b :: b1)) p) =
      b :: impl.huffman.find_code A a p

/-- Coq theorem `is_prefix_refl` translated as a proof obligation. -/
def spec_is_prefix_refl (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A], ∀ l : List Bool, is_prefix l l

/-- Coq theorem `not_in_find_code` translated as a proof obligation. -/
def spec_not_in_find_code (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A], ∀ (a : A) (l : Code A),
    (∀ p : List Bool, (a, p) ∉ l) → impl.huffman.find_code A a l = []

/-- Coq theorem `not_in_find_map` translated as a proof obligation. -/
def spec_not_in_find_map (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A], ∀ (p : Code A) (a : A) (b : Bool),
    (∀ l : List Bool, (a, l) ∉ p) →
    impl.huffman.find_code A a
      (List.map (fun v : A × List Bool => match v with | (a1, b1) => (a1, b :: b1)) p) = []

/-- Coq theorem `not_null_app` translated as a proof obligation. -/
def spec_not_null_app (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A], ∀ l1 l2 : List (A × List Bool),
    not_null l1 → not_null l2 → not_null (l1 ++ l2)

/-- Coq theorem `not_null_cons` translated as a proof obligation. -/
def spec_not_null_cons (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A], ∀ (a : A) (b : List Bool) (l : List (A × List Bool)),
    b ≠ [] → not_null l → not_null ((a, b) :: l)

/-- Coq theorem `not_null_find_val` translated as a proof obligation. -/
def spec_not_null_find_val (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A], ∀ c : Code A, not_null c → impl.huffman.find_val A [] c = none

/-- Coq theorem `not_null_inv` translated as a proof obligation. -/
def spec_not_null_inv (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A], ∀ (a : A × List Bool) (l : Code A),
    not_null (a :: l) → not_null l

/-- Coq theorem `not_null_map` translated as a proof obligation. -/
def spec_not_null_map (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A], ∀ (l : List (A × List Bool)) (b : Bool),
    not_null (List.map (fun v : A × List Bool => match v with | (a1, b1) => (a1, b :: b1)) l)

/-- Coq theorem `unique_prefix1` translated as a proof obligation. -/
def spec_unique_prefix1 (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A], ∀ (c : Code A) (a1 a2 : A) (lb1 lb2 : List Bool),
    unique_prefix c → (a1, lb1) ∈ c → (a2, lb2) ∈ c → is_prefix lb1 lb2 → a1 = a2

/-- Coq theorem `unique_prefix2` translated as a proof obligation. -/
def spec_unique_prefix2 (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A], ∀ c : Code A, unique_prefix c → unique_key c

/-- Coq theorem `unique_prefix_inv` translated as a proof obligation. -/
def spec_unique_prefix_inv (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A], ∀ (c : Code A) (a : A) (l : List Bool),
    unique_prefix ((a, l) :: c) → unique_prefix c

/-- Coq theorem `unique_prefix_nil` translated as a proof obligation. -/
def spec_unique_prefix_nil (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A], unique_prefix ([] : Code A)

/-- Coq theorem `unique_prefix_not_null` translated as a proof obligation. -/
def spec_unique_prefix_not_null (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A], ∀ (c : Code A) (a b : A),
    a ≠ b → in_alphabet (a :: b :: []) c → unique_prefix c → not_null c

/-- Coq theorem `unique_prefix_permutation` translated as a proof obligation. -/
def spec_unique_prefix_permutation (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A], ∀ c1 c2 : Code A,
    List.Perm c1 c2 → unique_prefix c1 → unique_prefix c2
