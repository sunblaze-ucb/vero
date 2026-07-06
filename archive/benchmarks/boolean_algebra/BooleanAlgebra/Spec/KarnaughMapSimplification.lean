import BooleanAlgebra.Harness

/-!
# BooleanAlgebra.Spec.KarnaughMapSimplification

Specifications for the Karnaugh map simplification function.

DO NOT MODIFY — frozen curator-given content.
-/

/-- An all-zero Karnaugh map simplifies to the empty string. -/
def spec_simplify_kmap_all_zero (impl : RepoImpl) : Prop :=
  impl.booleanAlgebra.simplify_kmap [[0, 0], [0, 0]] = ""

/-- Any all-zero Karnaugh map simplifies to the empty string. -/
def spec_simplify_kmap_all_zero_general (impl : RepoImpl) : Prop :=
  ∀ kmap : List (List Int),
    kmap.all (fun row => row.all (fun cell => decide (cell = 0))) = true →
    impl.booleanAlgebra.simplify_kmap kmap = ""

/-- The output depends only on zero vs. nonzero cell values, not the specific nonzero value. -/
def spec_simplify_kmap_nonzero_invariant (impl : RepoImpl) : Prop :=
  impl.booleanAlgebra.simplify_kmap [[0, 1], [1, -1]] =
    impl.booleanAlgebra.simplify_kmap [[0, 1], [1, 1]] ∧
  impl.booleanAlgebra.simplify_kmap [[0, 1], [1, 2]] =
    impl.booleanAlgebra.simplify_kmap [[0, 1], [1, 1]]

/-- Simplification depends on each cell only through whether it is zero or nonzero. -/
def spec_simplify_kmap_nonzero_normalization (impl : RepoImpl) : Prop :=
  ∀ kmap : List (List Int),
    impl.booleanAlgebra.simplify_kmap
      (kmap.map fun row => row.map fun cell => if cell = 0 then 0 else 1) =
    impl.booleanAlgebra.simplify_kmap kmap
