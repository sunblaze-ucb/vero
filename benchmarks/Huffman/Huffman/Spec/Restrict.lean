import Huffman.Harness
import Huffman.Impl.Restrict

/-!
# Huffman.Spec.Restrict

Frozen specifications translated from Coq's `Restrict.v`. Each `spec_*` is a
property over an arbitrary `impl : RepoImpl`.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- Coq theorem `frequency_list_restric_code_map` translated as a proof obligation. -/
def spec_frequency_list_restric_code_map (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A] (empty : A) (m : List A), ∀ c : Code A,
    List.map (fun p : A × Nat => p.1) (impl.huffman.frequency_list A m) =
      List.map (fun p : A × List Bool => p.1) (impl.huffman.restrict_code A m c)

/-- Coq theorem `restrict_code_encode` translated as a proof obligation. -/
def spec_restrict_code_encode (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A] (empty : A) (m : List A), ∀ c : Code A,
    impl.huffman.encode A c m =
      impl.huffman.encode A (impl.huffman.restrict_code A m c) m

/-- Coq theorem `restrict_code_encode_incl` translated as a proof obligation. -/
def spec_restrict_code_encode_incl (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A] (empty : A) (m : List A), ∀ (m1 : List A) (c : Code A),
    (∀ a : A, a ∈ m1 → a ∈ m) →
      impl.huffman.encode A c m1 =
        impl.huffman.encode A (impl.huffman.restrict_code A m c) m1

/-- Coq theorem `restrict_code_in` translated as a proof obligation. -/
def spec_restrict_code_in (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A] (empty : A) (m : List A), ∀ (a : A) (c : Code A),
    a ∈ m →
      impl.huffman.find_code A a c =
        impl.huffman.find_code A a (impl.huffman.restrict_code A m c)

/-- Coq theorem `restrict_code_pbbuild` translated as a proof obligation. -/
def spec_restrict_code_pbbuild (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A] (empty : A) (m : List A), ∀ c : Code A,
    not_null c →
      unique_prefix c →
        in_alphabet m c →
          m ≠ [] →
            List.Perm
              (List.map (fun p : A × Nat => p.1) (impl.huffman.frequency_list A m))
              (impl.huffman.all_pbleaves A
                (impl.huffman.pbbuild A empty (impl.huffman.restrict_code A m c)))

/-- Coq theorem `restrict_code_unique_key` translated as a proof obligation. -/
def spec_restrict_code_unique_key (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A] (empty : A) (m : List A), ∀ c : Code A,
    unique_key (impl.huffman.restrict_code A m c)

/-- Coq theorem `restrict_not_null` translated as a proof obligation. -/
def spec_restrict_not_null (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A] (empty : A) (m : List A), ∀ c : Code A,
    m ≠ [] → impl.huffman.restrict_code A m c ≠ []

/-- Coq theorem `restrict_unique_prefix` translated as a proof obligation. -/
def spec_restrict_unique_prefix (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A] (empty : A) (m : List A), ∀ c : Code A,
    not_null c →
      in_alphabet m c →
        unique_prefix c →
          unique_prefix (impl.huffman.restrict_code A m c)
