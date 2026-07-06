import Huffman.Harness
import Huffman.Impl.OrderedCover

/-!
# Huffman.Spec.OrderedCover

Frozen specifications translated from Coq's `OrderedCover.v`.

DO NOT MODIFY - this file is frozen curator-given content.
-/

/-- Coq theorem `NoDup_ordered_cover` translated as a proof obligation. -/
def spec_NoDup_ordered_cover (impl : RepoImpl) : Prop :=
  ∀ (A : Type), ∀ l1 l2 t,
    ordered_cover l1 t →
      List.Nodup l2 →
        l1 = List.map (fun x : A => BTree.leaf x) l2 →
          impl.huffman.all_leaves A t = l2

/-- Coq theorem `cover_ordered_cover` translated as a proof obligation. -/
def spec_cover_ordered_cover (impl : RepoImpl) : Prop :=
  ∀ (A : Type), ∀ (l1 : List (BTree A)) (t : BTree A),
    cover l1 t → ∃ l2, List.Perm l1 l2 ∧ ordered_cover l2 t

/-- Coq theorem `ordered_cover_cover` translated as a proof obligation. -/
def spec_ordered_cover_cover (impl : RepoImpl) : Prop :=
  ∀ (A : Type), ∀ (l : List (BTree A)) (t : BTree A), ordered_cover l t → cover l t
