import DedekindReals.Harness

/-!
# DedekindReals.Spec.Cauchy

Specifications for rational Cauchy sequences and their Dedekind-cut
interpretation. Each `spec_*` is a frozen property over an arbitrary
`impl : RepoImpl`.

DO NOT MODIFY -- this file is frozen curator-given content.
-/

open DedekindReals

/-- A rational sequence converging to a rational limit is Cauchy. -/
def spec_Un_cv_cauchy (impl : RepoImpl) : Prop :=
  ∀ (un : Nat → Rat) (l : Rat), Un_cv_Q un l → CauchyQ un

/-- The lower predicate associated with a Cauchy sequence is open. -/
def spec_CauchyQ_lower_open (impl : RepoImpl) : Prop :=
  ∀ (un : Nat → Rat) (q : Rat),
    CauchyQ_lower un q → ∃ r : Rat, q < r ∧ CauchyQ_lower un r

/-- The upper predicate associated with a Cauchy sequence is open. -/
def spec_CauchyQ_upper_open (impl : RepoImpl) : Prop :=
  ∀ (un : Nat → Rat) (r : Rat),
    CauchyQ_upper un r → ∃ q : Rat, q < r ∧ CauchyQ_upper un q

/-- A Cauchy sequence determines a located lower/upper cut split. -/
def spec_CauchyQ_located (impl : RepoImpl) : Prop :=
  ∀ (un : Nat → Rat) (q r : Rat),
    CauchyQ un → q < r → CauchyQ_lower un q ∨ CauchyQ_upper un r

/-- A series dominated by a Cauchy majorant series is Cauchy. -/
def spec_Cauchy_series_maj (impl : RepoImpl) : Prop :=
  ∀ (un vn : Nat → Rat), (∀ n : Nat, Rat.abs (un n) ≤ vn n) →
    CauchyQ (sum_f_Q0 vn) → CauchyQ (sum_f_Q0 un)
