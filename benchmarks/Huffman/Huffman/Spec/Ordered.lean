import Huffman.Harness
import Huffman.Impl.Ordered

/-!
# Huffman.Spec.Ordered

Frozen specifications translated from Coq's `Ordered.v`.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- Coq theorem `ordered_inv` translated as a proof obligation. -/
def spec_ordered_inv (impl : RepoImpl) : Prop :=
  ∀ (A : Type) (order : A → A → Prop), ∀ (a : A) (l : List A),
    ordered order (a :: l) → ordered order l

/-- Coq theorem `ordered_inv_order` translated as a proof obligation. -/
def spec_ordered_inv_order (impl : RepoImpl) : Prop :=
  ∀ (A : Type) (order : A → A → Prop), ∀ (a b : A) (l : List A),
    ordered order (a :: b :: l) → order a b

/-- Coq theorem `ordered_map_inv` translated as a proof obligation. -/
def spec_ordered_map_inv (impl : RepoImpl) : Prop :=
  ∀ (A B : Type) (order : A → A → Prop) (g : B → A) (l : List B),
    ordered (fun x y => order (g x) (g y)) l → ordered order (List.map g l)

/-- Coq theorem `ordered_perm_antisym_eq` translated as a proof obligation. -/
def spec_ordered_perm_antisym_eq (impl : RepoImpl) : Prop :=
  ∀ (A : Type) (order : A → A → Prop),
    (∀ a b c : A, order a b → order b c → order a c) →
    (∀ a b : A, order a b → order b a → a = b) →
    ∀ l1 l2 : List A, List.Perm l1 l2 → ordered order l1 → ordered order l2 → l1 = l2

/-- Coq theorem `ordered_skip` translated as a proof obligation. -/
def spec_ordered_skip (impl : RepoImpl) : Prop :=
  ∀ (A : Type) (order : A → A → Prop),
    (∀ a b c : A, order a b → order b c → order a c) →
    ∀ (a b : A) (l : List A),
      ordered order (a :: b :: l) → ordered order (a :: l)

/-- Coq theorem `ordered_trans` translated as a proof obligation. -/
def spec_ordered_trans (impl : RepoImpl) : Prop :=
  ∀ (A : Type) (order : A → A → Prop),
    (∀ a b c : A, order a b → order b c → order a c) →
    ∀ (a b : A) (l : List A),
      ordered order (a :: l) → b ∈ l → order a b

/-- Coq theorem `ordered_trans_app` translated as a proof obligation. -/
def spec_ordered_trans_app (impl : RepoImpl) : Prop :=
  ∀ (A : Type) (order : A → A → Prop),
    (∀ a b c : A, order a b → order b c → order a c) →
    ∀ (a b : A) (l1 l2 : List A),
      ordered order (l1 ++ l2) → a ∈ l1 → b ∈ l2 → order a b
