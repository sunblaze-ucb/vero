import Huffman.Harness
import Huffman.Impl.SameSumLeaves

/-!
# Huffman.Spec.SameSumLeaves

Frozen specifications translated from Coq's `SameSumLeaves.v`.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- Coq theorem `same_sum_leaves_length` translated as a proof obligation. -/
def spec_same_sum_leaves_length (impl : RepoImpl) : Prop :=
  ∀ (A : Type) (f : A → Nat), ∀ l1 l2 : List (BTree A),
    same_sum_leaves f l1 l2 → List.length l1 = List.length l2
