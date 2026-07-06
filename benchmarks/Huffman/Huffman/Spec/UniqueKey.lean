import Huffman.Harness
import Huffman.Impl.UniqueKey

/-!
# Huffman.Spec.UniqueKey

Frozen specifications translated from Coq's `UniqueKey.v`. Each
`spec_*` is a property over an arbitrary `impl : RepoImpl`.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- Coq theorem `NoDup_unique_key` translated as a proof obligation. -/
def spec_NoDup_unique_key (impl : RepoImpl) : Prop :=
  ∀ (A B : Type), ∀ l : List (A × B),
    List.Nodup (List.map Prod.fst l) → unique_key l

/-- Coq theorem `unique_key_NoDup` translated as a proof obligation. -/
def spec_unique_key_NoDup (impl : RepoImpl) : Prop :=
  ∀ (A B : Type), ∀ l : List (A × B),
    unique_key l → List.Nodup (List.map Prod.fst l)

/-- Coq theorem `unique_key_app` translated as a proof obligation. -/
def spec_unique_key_app (impl : RepoImpl) : Prop :=
  ∀ (A B : Type), ∀ (l1 l2 : List (A × B)),
    unique_key l1 →
    unique_key l2 →
    (∀ (a : A) (b c : B), (a, b) ∈ l1 → (a, c) ∈ l2 → False) →
    unique_key (l1 ++ l2)

/-- Coq theorem `unique_key_in` translated as a proof obligation. -/
def spec_unique_key_in (impl : RepoImpl) : Prop :=
  ∀ (A B : Type), ∀ (a : A) (b1 b2 : B) (l : List (A × B)),
    unique_key ((a, b1) :: l) → (a, b2) ∉ l

/-- Coq theorem `unique_key_in_inv` translated as a proof obligation. -/
def spec_unique_key_in_inv (impl : RepoImpl) : Prop :=
  ∀ (A B : Type), ∀ (a : A) (l1 l2 : B) (l : List (A × B)),
    unique_key l → (a, l1) ∈ l → (a, l2) ∈ l → l1 = l2

/-- Coq theorem `unique_key_inv` translated as a proof obligation. -/
def spec_unique_key_inv (impl : RepoImpl) : Prop :=
  ∀ (A B : Type), ∀ (a : A × B) (l : List (A × B)),
    unique_key (a :: l) → unique_key l

/-- Coq theorem `unique_key_map` translated as a proof obligation. -/
def spec_unique_key_map (impl : RepoImpl) : Prop :=
  ∀ (A B C D : Type), ∀ (l : List (A × B)) (f : A × B → C × D),
    unique_key l →
    (∀ (a b : A × B), Prod.fst (f a) = Prod.fst (f b) → Prod.fst a = Prod.fst b) →
    unique_key (List.map f l)

/-- Coq theorem `unique_key_perm` translated as a proof obligation. -/
def spec_unique_key_perm (impl : RepoImpl) : Prop :=
  ∀ (A B : Type), ∀ (l1 l2 : List (A × B)),
    List.Perm l1 l2 → unique_key l1 → unique_key l2
