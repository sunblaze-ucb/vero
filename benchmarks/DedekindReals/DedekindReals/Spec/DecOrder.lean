import DedekindReals.Harness

/-!
# DedekindReals.Spec.DecOrder

Specifications for decidable-order consequences on Dedekind cuts. Each
`spec_*` is a frozen property over an arbitrary `impl : RepoImpl`.

DO NOT MODIFY -- this file is frozen curator-given content.
-/

open DedekindReals

/-- A decidable strict order on Dedekind reals implies LPO. -/
def spec_DecOrderImpliesLPO (impl : RepoImpl) : Prop :=
  (∀ x : R,
    (impl.dedekindReals.Rlt (impl.dedekindReals.R_of_Q 0) x) ∨
      ¬ (impl.dedekindReals.Rlt (impl.dedekindReals.R_of_Q 0) x)) →
    LPO
