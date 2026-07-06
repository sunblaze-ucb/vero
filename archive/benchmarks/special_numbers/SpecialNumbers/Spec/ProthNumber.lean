import SpecialNumbers.Harness

/-!
# SpecialNumbers.Spec.ProthNumber

Specifications for Proth numbers.
Each `spec_*` is a property over an arbitrary `impl : RepoImpl`.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- Valid Proth sequence positions produce positive odd numbers. -/
def spec_proth_positive_odd (impl : RepoImpl) : Prop :=
  ∀ n : Int, n > 0 →
    impl.specialNumbers.proth n > 0 ∧
    impl.specialNumbers.proth n % 2 = 1

/-- Sentinel behavior: `proth` returns 0 for non-positive indices (Python ValueError analogue).
    Complements `spec_proth_positive_odd`, which only constrains the positive domain. -/
def spec_proth_invalid (impl : RepoImpl) : Prop :=
  ∀ n : Int, n ≤ 0 → impl.specialNumbers.proth n = 0
