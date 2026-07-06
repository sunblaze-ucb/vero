import DedekindReals.Harness

/-!
# DedekindReals.Spec.Completeness

Specifications for Dedekind completeness. Each `spec_*` is a frozen property
over an arbitrary `impl : RepoImpl`.

DO NOT MODIFY -- this file is frozen curator-given content.
-/

open DedekindReals

/-- Equality of real cuts is reflexive. -/
def spec_RCut_eq_refl (impl : RepoImpl) : Prop :=
  ∀ c : RCut, RCut_eq c c

/-- Equality of real cuts is symmetric. -/
def spec_RCut_eq_sym (impl : RepoImpl) : Prop :=
  ∀ c d : RCut, RCut_eq c d → RCut_eq d c

/-- Equality of real cuts is transitive. -/
def spec_RCut_eq_trans (impl : RepoImpl) : Prop :=
  ∀ c d e : RCut, RCut_eq c d → RCut_eq d e → RCut_eq c e

/-- Every real cut is represented by the real obtained from it. -/
def spec_dedekind_complete (impl : RepoImpl) : Prop :=
  ∀ c : RCut,
    RCut_eq c ((impl.dedekindReals.RCut_of_R (impl.dedekindReals.R_of_RCut c)))
