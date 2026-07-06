import Huffman.Harness
import Huffman.Impl.HeightPred

/-!
# Huffman.Spec.HeightPred

Specifications for height-list predicates over Huffman tree covers. Each
`spec_*` is a property over an arbitrary `impl : RepoImpl`.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- Computed codes induce a height predicate over their code lengths and leaves. -/
def spec_height_pred_compute_code (impl : RepoImpl) : Prop :=
  ∀ (A : Type) (f : A → Nat), ∀ (n : Nat) (t : BTree A),
    height_pred n
      (List.map (fun x => List.length (Prod.snd x) + n) (impl.huffman.compute_code A t))
      (List.map (fun x => BTree.leaf (Prod.fst x)) (impl.huffman.compute_code A t))
      t

/-- A selected height is either dominated elsewhere or is the singleton base case. -/
def spec_height_pred_disj_larger2 (impl : RepoImpl) : Prop :=
  ∀ (A : Type) (f : A → Nat), ∀ (n a : Nat) (ln1 ln2 : List Nat) (t : BTree A) (l : List (BTree A)),
    height_pred n (ln1 ++ a :: ln2) l t →
      (∃ n1, n1 ∈ ln1 ∧ a ≤ n1) ∨
        (∃ n1, n1 ∈ ln2 ∧ a ≤ n1) ∨
          (ln1 = [] ∧ a = n ∧ ln2 = []) ∧ l = t :: []

/-- If earlier heights are smaller and later heights are bounded, the maximum repeats or the base case holds. -/
def spec_height_pred_disj_larger (impl : RepoImpl) : Prop :=
  ∀ (A : Type) (f : A → Nat), ∀ (n a : Nat) (ln1 ln2 : List Nat) (t : BTree A) (l : List (BTree A)),
    height_pred n (ln1 ++ a :: ln2) l t →
      (∀ n1 : Nat, n1 ∈ ln1 → n1 < a) →
        (∀ n1 : Nat, n1 ∈ ln2 → n1 ≤ a) →
          (∃ ln3, ln2 = a :: ln3) ∨
            (ln1 = [] ∧ a = n ∧ ln2 = []) ∧ l = t :: []

/-- Every height in the list is at least the initial height. -/
def spec_height_pred_larger (impl : RepoImpl) : Prop :=
  ∀ (A : Type) (f : A → Nat), ∀ (n n1 : Nat) (ln : List Nat) (t : BTree A) (l : List (BTree A)),
    height_pred n ln l t → n1 ∈ ln → n ≤ n1

/-- A height predicate always contains some height at least the initial height. -/
def spec_height_pred_larger_ex (impl : RepoImpl) : Prop :=
  ∀ (A : Type) (f : A → Nat), ∀ (n : Nat) (ln : List Nat) (t : BTree A) (l : List (BTree A)),
    height_pred n ln l t → ∃ n1, n1 ∈ ln ∧ n ≤ n1

/-- Heights are strictly larger than the initial height unless this is the singleton base case. -/
def spec_height_pred_larger_strict (impl : RepoImpl) : Prop :=
  ∀ (A : Type) (f : A → Nat), ∀ (n n1 : Nat) (ln : List Nat) (t : BTree A) (l : List (BTree A)),
    height_pred n ln l t → n1 ∈ ln → n < n1 ∨ ln = n :: [] ∧ l = t :: []

/-- Height and cover lists have equal length. -/
def spec_height_pred_length (impl : RepoImpl) : Prop :=
  ∀ (A : Type) (f : A → Nat), ∀ (n : Nat) (ln : List Nat) (t : BTree A) (l : List (BTree A)),
    height_pred n ln l t → List.length ln = List.length l

/-- A height list in a height predicate is nonempty. -/
def spec_height_pred_not_nil1 (impl : RepoImpl) : Prop :=
  ∀ (A : Type) (f : A → Nat), ∀ (n : Nat) (ln : List Nat) (t : BTree A) (l : List (BTree A)),
    height_pred n ln l t → ln ≠ []

/-- A cover list in a height predicate is nonempty. -/
def spec_height_pred_not_nil2 (impl : RepoImpl) : Prop :=
  ∀ (A : Type) (f : A → Nat), ∀ (n : Nat) (ln : List Nat) (t : BTree A) (l : List (BTree A)),
    height_pred n ln l t → l ≠ []

/-- A height predicate implies the associated cover is ordered. -/
def spec_height_pred_ordered_cover (impl : RepoImpl) : Prop :=
  ∀ (A : Type) (f : A → Nat), ∀ (n : Nat) (ln : List Nat) (t : BTree A) (l : List (BTree A)),
    height_pred n ln l t → ordered_cover l t

/-- Shrinking adjacent maximum heights preserves the height predicate. -/
def spec_height_pred_shrink (impl : RepoImpl) : Prop :=
  ∀ (A : Type) (f : A → Nat), ∀ (n a b : Nat) (ln1 ln2 : List Nat) (t t1 t2 : BTree A) (l1 l2 : List (BTree A)),
    height_pred n (ln1 ++ a :: b :: ln2) (l1 ++ t1 :: t2 :: l2) t →
      (∀ n1 : Nat, n1 ∈ ln1 → n1 < a) →
        (∀ n1 : Nat, n1 ∈ (b :: ln2) → n1 ≤ a) →
          List.length ln1 = List.length l1 →
            height_pred n (ln1 ++ Nat.pred a :: ln2) (l1 ++ BTree.node t1 t2 :: l2) t

/-- Height predicates characterize the weighted product relation. -/
def spec_height_pred_weight (impl : RepoImpl) : Prop :=
  ∀ (A : Type) (f : A → Nat), ∀ (n : Nat) (ln : List Nat) (t : BTree A) (l : List (BTree A)),
    height_pred n ln l t →
      n * impl.huffman.sum_leaves A f t + impl.huffman.weight_tree A f t =
        impl.huffman.prod2list A f ln l

/-- Every ordered cover admits a height list. -/
def spec_ordered_cover_height_pred (impl : RepoImpl) : Prop :=
  ∀ (A : Type) (f : A → Nat), ∀ (n : Nat) (t : BTree A) (l : List (BTree A)),
    ordered_cover l t → ∃ ln : List Nat, height_pred n ln l t

/-- Encoding with a tree's computed code has length equal to the tree weight. -/
def spec_weight_tree_compute (impl : RepoImpl) : Prop :=
  ∀ (A : Type) [DecidableEq A] (f : A → Nat), ∀ (m : List A) t,
    distinct_leaves t →
      (∀ a : A, f a = impl.huffman.number_of_occurrences A a m) →
        List.length (impl.huffman.encode A (impl.huffman.compute_code A t) m) =
          impl.huffman.weight_tree A f t
