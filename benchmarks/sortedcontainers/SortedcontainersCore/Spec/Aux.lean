import SortedcontainersCore.Harness

/-!
# SortedcontainersCore.Spec.Aux

Shared predicates used by the curated specifications.
-/

/-- True when a list is non-strictly sorted according to its `Ord` instance. -/
def spec_helper_sortedByOrd {α : Type} [Ord α] : List α → Prop
  | [] => True
  | [_] => True
  | x :: y :: xs =>
      (Ord.compare x y = Ordering.lt ∨ Ord.compare x y = Ordering.eq) ∧
      spec_helper_sortedByOrd (y :: xs)

/-- Every element of `xs` also occurs in `ys`. -/
def spec_helper_containsAll {α : Type} (xs ys : List α) : Prop :=
  ∀ x, x ∈ xs → x ∈ ys

/-- Count occurrences of a natural number in a list. -/
def spec_helper_countNat (x : Nat) : List Nat → Nat
  | [] => 0
  | y :: ys => (if x == y then 1 else 0) + spec_helper_countNat x ys
