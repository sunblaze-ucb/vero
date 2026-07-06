import Bidict.Harness

/-!
# Bidict.Spec.Exc

Specifications for the duplication error vocabulary (`DuplicationError`).
Each `spec_*` is a property over an arbitrary `impl : RepoImpl`. These
specs do not depend on any `impl` field — they assert that the three
duplication error constructors are pairwise distinct (so that callers
can pattern-match unambiguously on the error variant).

DO NOT MODIFY — frozen curator-given content.
-/

/-- `duplicateKeyError` is distinct from `duplicateValueError`: the two
    constructors carry different semantic meanings and must not collapse. -/
def spec_duplicateKeyError_distinct (_impl : RepoImpl) : Prop :=
  DuplicationError.duplicateKeyError ≠ DuplicationError.duplicateValueError

/-- `duplicateValueError` is distinct from `duplicateKeyError` (symmetric to
    the previous obligation; expressed independently for ergonomic use). -/
def spec_duplicateValueError_distinct (_impl : RepoImpl) : Prop :=
  DuplicationError.duplicateValueError ≠ DuplicationError.duplicateKeyError

/-- `duplicateKeyAndValueError` is distinct from both single-axis duplicate
    constructors: it represents a strictly different (combined) failure mode. -/
def spec_duplicateKeyAndValueError_distinct (_impl : RepoImpl) : Prop :=
  DuplicationError.duplicateKeyAndValueError ≠ DuplicationError.duplicateKeyError ∧
  DuplicationError.duplicateKeyAndValueError ≠ DuplicationError.duplicateValueError
