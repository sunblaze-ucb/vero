import Huffman.Harness
import Huffman.Impl.SubstPred

/-!
# Huffman.Spec.SubstPred

Frozen specifications translated from Coq's `SubstPred.v`.

DO NOT MODIFY - this file is frozen curator-given content.
-/

/-- Coq theorem `height_pred_subst_pred` translated as a proof obligation. -/
def spec_height_pred_subst_pred (impl : RepoImpl) : Prop :=
  ∀ (A : Type), ∀ (n : Nat) (ln : List Nat) (t1 : BTree A) (l1 l2 : List (BTree A)), height_pred n ln l1 t1 → List.length l1 = List.length l2 → ∃ t2 : BTree A, height_pred n ln l2 t2 ∧ subst_pred l1 l2 t1 t2

/-- Coq theorem `ordered_cover_subst_pred` translated as a proof obligation. -/
def spec_ordered_cover_subst_pred (impl : RepoImpl) : Prop :=
  ∀ (A : Type), ∀ (t1 : BTree A) (l1 l2 : List (BTree A)), ordered_cover l1 t1 → List.length l1 = List.length l2 → ∃ t2 : BTree A, subst_pred l1 l2 t1 t2

/-- Coq theorem `subst_pred_length` translated as a proof obligation. -/
def spec_subst_pred_length (impl : RepoImpl) : Prop :=
  ∀ (A : Type), ∀ (t1 t2 : BTree A) (l1 l2 : List (BTree A)), subst_pred l1 l2 t1 t2 → List.length l1 = List.length l2

/-- Coq theorem `subst_pred_ordered_cover_l` translated as a proof obligation. -/
def spec_subst_pred_ordered_cover_l (impl : RepoImpl) : Prop :=
  ∀ (A : Type), ∀ (t1 t2 : BTree A) (l1 l2 : List (BTree A)), subst_pred l1 l2 t1 t2 → ordered_cover l1 t1

/-- Coq theorem `subst_pred_ordered_cover_r` translated as a proof obligation. -/
def spec_subst_pred_ordered_cover_r (impl : RepoImpl) : Prop :=
  ∀ (A : Type), ∀ (t1 t2 : BTree A) (l1 l2 : List (BTree A)), subst_pred l1 l2 t1 t2 → ordered_cover l2 t2
