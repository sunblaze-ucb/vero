import Huffman.Harness
import Huffman.Impl.CoverMin

/-!
# Huffman.Spec.CoverMin

Frozen specifications translated from Coq's `CoverMin.v`.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- Coq theorem `cover_min_ex` translated as a proof obligation. -/
def spec_cover_min_ex (impl : RepoImpl) : Prop :=
  ∀ (A : Type) (f : A → Nat), ∀ l : List (BTree A),
    l ≠ [] → ∃ t : BTree A, cover_min A f l t

/-- Coq theorem `cover_min_one` translated as a proof obligation. -/
def spec_cover_min_one (impl : RepoImpl) : Prop :=
  ∀ (A : Type) (f : A → Nat), ∀ t : BTree A, cover_min A f (t :: []) t

/-- Coq theorem `cover_min_permutation` translated as a proof obligation. -/
def spec_cover_min_permutation (impl : RepoImpl) : Prop :=
  ∀ (A : Type) (f : A → Nat), ∀ (t : BTree A) (l1 l2 : List (BTree A)),
    cover_min A f l1 t → List.Perm l1 l2 → cover_min A f l2 t
