import DedekindReals.Harness

/-!
# DedekindReals.Spec.Archimedean

Specifications for Archimedean rational approximation. Each `spec_*` is a
frozen property over an arbitrary `impl : RepoImpl`.

DO NOT MODIFY -- this file is frozen curator-given content.
-/

open DedekindReals

/-- Every real cut is straddled by rationals with any positive rational gap. -/
def spec_archimedean (_impl : RepoImpl) : Prop :=
  ∀ (x : R) (q : Rat), 0 < q → straddle x q
