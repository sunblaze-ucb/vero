import DedekindReals.Harness

/-!
# DedekindReals.Spec.Order

Specifications for order relations on Dedekind cuts. Each `spec_*` is a
frozen property over an arbitrary `impl : RepoImpl`.

DO NOT MODIFY -- this file is frozen curator-given content.
-/

open DedekindReals

/-- Strict order is irreflexive. -/
def spec_Rlt_irrefl (impl : RepoImpl) : Prop :=
  ∀ (x : R), ¬ (impl.dedekindReals.Rlt x x)

/-- Strict order is transitive. -/
def spec_Rlt_trans (impl : RepoImpl) : Prop :=
  ∀ (x y z : R), (impl.dedekindReals.Rlt x y) → (impl.dedekindReals.Rlt y z) →
    (impl.dedekindReals.Rlt x z)

/-- Strict order is asymmetric. -/
def spec_Rlt_asymm (impl : RepoImpl) : Prop :=
  ∀ x y : R, ¬ ((impl.dedekindReals.Rlt x y) ∧ (impl.dedekindReals.Rlt y x))

/-- Strict order is cotransitive in the right argument. -/
def spec_Rlt_linear (impl : RepoImpl) : Prop :=
  ∀ (x y z : R), (impl.dedekindReals.Rlt x y) →
    (impl.dedekindReals.Rlt x z) ∨ (impl.dedekindReals.Rlt z y)

/-- Apartness is symmetric. -/
def spec_Rneq_symm (impl : RepoImpl) : Prop :=
  ∀ x y : R, (impl.dedekindReals.Rneq x y) → (impl.dedekindReals.Rneq y x)

/-- Apartness is irreflexive. -/
def spec_Rneq_irrefl (impl : RepoImpl) : Prop :=
  ∀ x : R, (impl.dedekindReals.Rneq x x) → False

/-- Apartness is cotransitive. -/
def spec_Rnew_contrans (impl : RepoImpl) : Prop :=
  ∀ x y z : R, (impl.dedekindReals.Rneq x y) →
    ((impl.dedekindReals.Rneq x z) ∨ (impl.dedekindReals.Rneq y z))

/-- Non-strict order is reflexive. -/
def spec_Rle_refl (impl : RepoImpl) : Prop :=
  ∀ (x : R), (impl.dedekindReals.Rle x x)

/-- Non-strict order is transitive. -/
def spec_Rle_trans (impl : RepoImpl) : Prop :=
  ∀ (x y z : R), (impl.dedekindReals.Rle x y) → (impl.dedekindReals.Rle y z) →
    (impl.dedekindReals.Rle x z)

/-- Non-strict order is antisymmetric up to real equality. -/
def spec_Rle_antisym (impl : RepoImpl) : Prop :=
  ∀ (x y : R), (impl.dedekindReals.Rle x y) → (impl.dedekindReals.Rle y x) →
    (impl.dedekindReals.Req x y)

/-- Strict order implies non-strict order. -/
def spec_Rlt_le_weak (impl : RepoImpl) : Prop :=
  ∀ (x y : R), (impl.dedekindReals.Rlt x y) → (impl.dedekindReals.Rle x y)

/-- Negated strict order is equivalent to reverse non-strict order. -/
def spec_Order_Rnot_lt_le (impl : RepoImpl) : Prop :=
  ∀ (r1 r2 : R), ¬ (impl.dedekindReals.Rlt r1 r2) ↔ (impl.dedekindReals.Rle r2 r1)

/-- Zero is strictly less than one. -/
def spec_R0_lt_1 (impl : RepoImpl) : Prop :=
  impl.dedekindReals.Rlt (impl.dedekindReals.R_of_Q 0) (impl.dedekindReals.R_of_Q 1)

/-- Strict order is compatible with adding the same value on the right. -/
def spec_Rplus_lt_compat_r (impl : RepoImpl) : Prop :=
  ∀ (x y z : R), (impl.dedekindReals.Rlt x y) ↔
    (impl.dedekindReals.Rlt (impl.dedekindReals.Rplus x z) (impl.dedekindReals.Rplus y z))

/-- Strict order is compatible with adding the same value on the left. -/
def spec_Rplus_lt_compat_l (impl : RepoImpl) : Prop :=
  ∀ (x y z : R), (impl.dedekindReals.Rlt y z) ↔
    (impl.dedekindReals.Rlt (impl.dedekindReals.Rplus x y) (impl.dedekindReals.Rplus x z))

/-- Non-strict order is compatible with adding the same value on the right. -/
def spec_Order_Rplus_le_compat_r (impl : RepoImpl) : Prop :=
  ∀ (x y z : R), (impl.dedekindReals.Rle x y) ↔
    (impl.dedekindReals.Rle (impl.dedekindReals.Rplus x z) (impl.dedekindReals.Rplus y z))

/-- Non-strict order is compatible with adding the same value on the left. -/
def spec_Order_Rplus_le_compat_l (impl : RepoImpl) : Prop :=
  ∀ (x y z : R), (impl.dedekindReals.Rle y z) ↔
    (impl.dedekindReals.Rle (impl.dedekindReals.Rplus x y) (impl.dedekindReals.Rplus x z))

/-- If a sum is positive, at least one summand is positive. -/
def spec_Rplus_positive (impl : RepoImpl) : Prop :=
  ∀ (x y : R),
    (impl.dedekindReals.Rlt (impl.dedekindReals.R_of_Q 0) (impl.dedekindReals.Rplus x y)) →
      (impl.dedekindReals.Rlt (impl.dedekindReals.R_of_Q 0) x) ∨
        (impl.dedekindReals.Rlt (impl.dedekindReals.R_of_Q 0) y)

/-- Multiplication by a nonnegative value on the right preserves non-strict order. -/
def spec_Rmult_le_compat_r (impl : RepoImpl) : Prop :=
  ∀ (x y z : R), (impl.dedekindReals.Rle (impl.dedekindReals.R_of_Q 0) z) →
    (impl.dedekindReals.Rle x y) →
      (impl.dedekindReals.Rle (impl.dedekindReals.Rmult x z) (impl.dedekindReals.Rmult y z))

/-- Multiplication by a nonnegative value on the left preserves non-strict order. -/
def spec_Rmult_le_compat_l (impl : RepoImpl) : Prop :=
  ∀ (x y z : R), (impl.dedekindReals.Rle (impl.dedekindReals.R_of_Q 0) x) →
    (impl.dedekindReals.Rle y z) →
      (impl.dedekindReals.Rle (impl.dedekindReals.Rmult x y) (impl.dedekindReals.Rmult x z))

/-- Multiplication by a positive value on the right reflects and preserves strict order. -/
def spec_Rmult_lt_compat_r (impl : RepoImpl) : Prop :=
  ∀ (x y z : R), (impl.dedekindReals.Rlt (impl.dedekindReals.R_of_Q 0) z) →
    ((impl.dedekindReals.Rlt x y) ↔
      (impl.dedekindReals.Rlt (impl.dedekindReals.Rmult x z) (impl.dedekindReals.Rmult y z)))

/-- Multiplication by a positive value on the left reflects and preserves strict order. -/
def spec_Rmult_lt_compat_l (impl : RepoImpl) : Prop :=
  ∀ (x y z : R), (impl.dedekindReals.Rlt (impl.dedekindReals.R_of_Q 0) x) →
    ((impl.dedekindReals.Rlt y z) ↔
      (impl.dedekindReals.Rlt (impl.dedekindReals.Rmult x y) (impl.dedekindReals.Rmult x z)))
