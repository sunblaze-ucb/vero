import Huffman.Harness
import Huffman.Impl.Huffman

/-!
# Huffman.Spec.Huffman

Frozen specifications translated from Coq's `Huffman.v`.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- Coq theorem `huffman_build_minimum` translated as a proof obligation. -/
def spec_huffman_build_minimum (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A] (empty : A) (m : List A),
    ∀ (c : Code A) (t : BTree A),
      unique_prefix c →
      in_alphabet m c →
      build
        (fun x => impl.huffman.number_of_occurrences A x m)
        (List.map (fun x => BTree.leaf (Prod.fst x)) (impl.huffman.frequency_list A m))
        t →
      impl.huffman.weight A m (impl.huffman.compute_code A t) ≤
        impl.huffman.weight A m c

/-- Coq theorem `not_null_m` translated as a proof obligation. -/
def spec_not_null_m (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A] (empty : A) (m : List A), m ≠ []
