import Huffman.Harness
import Huffman.Impl.ISort
import Huffman.Impl.Ordered

/-!
# Huffman.Spec.ISort

Frozen specifications translated from Coq's `ISort.v`.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- Coq theorem `insert_ordered` translated as a proof obligation. -/
def spec_insert_ordered (impl : RepoImpl) : Prop :=
  ∀ (A : Type) (order : A → A → Prop) (order_fun : A → A → Bool),
    (∀ a b : A, order_fun a b = true → order a b) →
    (∀ a b : A, order_fun a b = false → order b a) →
    ∀ l : List A, ordered order l → ∀ a : A,
      ordered order (impl.huffman.insert A order_fun a l)

/-- Coq theorem `insert_permutation` translated as a proof obligation. -/
def spec_insert_permutation (impl : RepoImpl) : Prop :=
  ∀ (A : Type) (order : A → A → Prop) (order_fun : A → A → Bool),
    ∀ (L : List A) (a : A),
      List.Perm (a :: L) (impl.huffman.insert A order_fun a L)

/-- Coq theorem `isort_ordered` translated as a proof obligation. -/
def spec_isort_ordered (impl : RepoImpl) : Prop :=
  ∀ (A : Type) (order : A → A → Prop) (order_fun : A → A → Bool),
    (∀ a b : A, order_fun a b = true → order a b) →
    (∀ a b : A, order_fun a b = false → order b a) →
    ∀ l : List A, ordered order (impl.huffman.isort A order_fun l)

/-- Coq theorem `isort_permutation` translated as a proof obligation. -/
def spec_isort_permutation (impl : RepoImpl) : Prop :=
  ∀ (A : Type) (order : A → A → Prop) (order_fun : A → A → Bool),
    ∀ l : List A, List.Perm l (impl.huffman.isort A order_fun l)
