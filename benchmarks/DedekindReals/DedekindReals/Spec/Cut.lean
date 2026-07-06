import DedekindReals.Harness

/-!
# DedekindReals.Spec.Cut

Specifications for Dedekind cuts. Each `spec_*` is a frozen property over an
arbitrary `impl : RepoImpl`.

DO NOT MODIFY -- this file is frozen curator-given content.
-/

open DedekindReals

/-- Non-strict order by lower cuts is equivalent to non-strict order by upper cuts. -/
def spec_Rle_equiv (impl : RepoImpl) : Prop :=
  ∀ (x y : R), (impl.dedekindReals.Rle x y) ↔ Rle_upper x y

/-- Negated strict order is equivalent to the reverse non-strict order. -/
def spec_Rnot_lt_le (impl : RepoImpl) : Prop :=
  ∀ (r1 r2 : R), ¬ (impl.dedekindReals.Rlt r1 r2) ↔ (impl.dedekindReals.Rle r2 r1)

/-- Equality by lower cuts is equivalent to equality by upper cuts. -/
def spec_Req_equiv (impl : RepoImpl) : Prop :=
  ∀ (x y : R), (impl.dedekindReals.Req x y) ↔ Req_upper x y

/-- Any lower-bound rational is strictly below any upper-bound rational. -/
def spec_lower_below_upper (_impl : RepoImpl) : Prop :=
  ∀ (x : R) (q r : Rat), x.lower q → x.upper r → q < r

/-- Lower cuts are downward closed for non-strict rational order. -/
def spec_lower_le (_impl : RepoImpl) : Prop :=
  ∀ (x : R) (q r : Rat), x.lower r → q ≤ r → x.lower q

/-- Upper cuts are upward closed for non-strict rational order. -/
def spec_upper_le (_impl : RepoImpl) : Prop :=
  ∀ (x : R) (q r : Rat), x.upper q → q ≤ r → x.upper r

/-- A rational is in the upper cut exactly when the cut is below that rational. -/
def spec_R_lt_Q_iff (impl : RepoImpl) : Prop :=
  ∀ (x : R) (q : Rat),
    x.upper q ↔ (impl.dedekindReals.Rlt x (impl.dedekindReals.R_of_Q q))

/-- Characterization of when a cut is equal to a rational cut. -/
def spec_R_is_Q_iff (impl : RepoImpl) : Prop :=
  ∀ (x : R) (q : Rat),
    (impl.dedekindReals.Req x (impl.dedekindReals.R_of_Q q)) ↔
      (∀ r : Rat, (q < r → x.upper r) ∧ (r < q → x.lower r))
