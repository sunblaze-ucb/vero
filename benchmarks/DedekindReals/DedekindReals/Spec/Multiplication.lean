import DedekindReals.Harness

/-!
# DedekindReals.Spec.Multiplication

Specifications for multiplication and inverse on Dedekind cuts. Each
`spec_*` is a frozen property over an arbitrary `impl : RepoImpl`.

DO NOT MODIFY -- this file is frozen curator-given content.
-/

open DedekindReals

/-- The lower cut of a product is open upward. -/
def spec_mult_lower_open (_impl : RepoImpl) : Prop :=
  let multLower := fun (x y : R) (q : Rat) =>
    ∃ a b c d : Rat,
      x.lower a ∧ x.upper b ∧ y.lower c ∧ y.upper d ∧
        q < Qmin4 (a * c) (a * d) (b * c) (b * d)
  ∀ (x y : R) (q : Rat), multLower x y q → ∃ r : Rat, q < r ∧ multLower x y r

/-- The upper cut of a product is open downward. -/
def spec_mult_upper_open (_impl : RepoImpl) : Prop :=
  let multUpper := fun (x y : R) (q : Rat) =>
    ∃ a b c d : Rat,
      x.lower a ∧ x.upper b ∧ y.lower c ∧ y.upper d ∧
        Qmax4 (a * c) (a * d) (b * c) (b * d) < q
  ∀ (x y : R) (q : Rat), multUpper x y q → ∃ r : Rat, r < q ∧ multUpper x y r

/-- The product cut can be located by sufficiently small rational intervals. -/
def spec_DReal_locate_mult (_impl : RepoImpl) : Prop :=
  ∀ (x y : R) (eta : Rat), 0 < eta →
    ∃ eps a b : Rat,
      0 < eps ∧ x.lower a ∧ x.upper (a + eps) ∧ y.lower b ∧ y.upper (b + eps) ∧
        Qmax4 (a * b) (a * (b + eps)) ((a + eps) * b) ((a + eps) * (b + eps)) -
            Qmin4 (a * b) (a * (b + eps)) ((a + eps) * b) ((a + eps) * (b + eps)) <
          eta

/-- Multiplication is commutative. -/
def spec_Rmult_comm (impl : RepoImpl) : Prop :=
  ∀ (x y : R),
    impl.dedekindReals.Req
      (impl.dedekindReals.Rmult x y)
      (impl.dedekindReals.Rmult y x)

/-- One is a left identity for multiplication. -/
def spec_Rmult_1_l (impl : RepoImpl) : Prop :=
  ∀ (x : R),
    impl.dedekindReals.Req
      (impl.dedekindReals.Rmult (impl.dedekindReals.R_of_Q 1) x)
      x

/-- One is a right identity for multiplication. -/
def spec_Rmult_1_r (impl : RepoImpl) : Prop :=
  ∀ (x : R),
    impl.dedekindReals.Req
      (impl.dedekindReals.Rmult x (impl.dedekindReals.R_of_Q 1))
      x

/-- Negating a product is the same as negating the left factor. -/
def spec_Ropp_mult_distr_l (impl : RepoImpl) : Prop :=
  ∀ (r1 r2 : R),
    impl.dedekindReals.Req
      (impl.dedekindReals.Ropp (impl.dedekindReals.Rmult r1 r2))
      (impl.dedekindReals.Rmult (impl.dedekindReals.Ropp r1) r2)

/-- Negating a product is the same as negating the right factor. -/
def spec_Ropp_mult_distr_r (impl : RepoImpl) : Prop :=
  ∀ (r1 r2 : R),
    impl.dedekindReals.Req
      (impl.dedekindReals.Ropp (impl.dedekindReals.Rmult r1 r2))
      (impl.dedekindReals.Rmult r1 (impl.dedekindReals.Ropp r2))

/-- Right distributivity holds as a non-strict inequality. -/
def spec_Rmult_plus_distr_r_le (impl : RepoImpl) : Prop :=
  ∀ (x y z : R),
    impl.dedekindReals.Rle
      (impl.dedekindReals.Rplus
        (impl.dedekindReals.Rmult x y)
        (impl.dedekindReals.Rmult x z))
      (impl.dedekindReals.Rmult x (impl.dedekindReals.Rplus y z))

/-- Multiplication distributes over addition on the right. -/
def spec_Rmult_plus_distr_r (impl : RepoImpl) : Prop :=
  ∀ (x y z : R),
    impl.dedekindReals.Req
      (impl.dedekindReals.Rmult x (impl.dedekindReals.Rplus y z))
      (impl.dedekindReals.Rplus
        (impl.dedekindReals.Rmult x y)
        (impl.dedekindReals.Rmult x z))

/-- Multiplication distributes over addition on the left. -/
def spec_Rmult_plus_distr_l (impl : RepoImpl) : Prop :=
  ∀ (x y z : R),
    impl.dedekindReals.Req
      (impl.dedekindReals.Rmult (impl.dedekindReals.Rplus x y) z)
      (impl.dedekindReals.Rplus
        (impl.dedekindReals.Rmult x z)
        (impl.dedekindReals.Rmult y z))

/-- For positive factors, the product lower cut is characterized by positive lower witnesses. -/
def spec_mult_lower_pos (impl : RepoImpl) : Prop :=
  let multLower := fun (x y : R) (q : Rat) =>
    ∃ a b c d : Rat,
      x.lower a ∧ x.upper b ∧ y.lower c ∧ y.upper d ∧
        q < Qmin4 (a * c) (a * d) (b * c) (b * d)
  ∀ x y : R,
    impl.dedekindReals.Rlt (impl.dedekindReals.R_of_Q 0) x →
      impl.dedekindReals.Rlt (impl.dedekindReals.R_of_Q 0) y →
        ∀ q : Rat,
          multLower x y q ↔
            ∃ r s : Rat, 0 < r ∧ 0 < s ∧ x.lower r ∧ y.lower s ∧ q < r * s

/-- The product of two positive reals is positive. -/
def spec_Rmult_lt_0_compat (impl : RepoImpl) : Prop :=
  ∀ r1 r2 : R,
    impl.dedekindReals.Rlt (impl.dedekindReals.R_of_Q 0) r1 →
      impl.dedekindReals.Rlt (impl.dedekindReals.R_of_Q 0) r2 →
        impl.dedekindReals.Rlt
          (impl.dedekindReals.R_of_Q 0)
          (impl.dedekindReals.Rmult r1 r2)

/-- Multiplication is associative for positive factors. -/
def spec_Rmult_assoc_pos (impl : RepoImpl) : Prop :=
  ∀ (x y z : R),
    impl.dedekindReals.Rlt (impl.dedekindReals.R_of_Q 0) x →
      impl.dedekindReals.Rlt (impl.dedekindReals.R_of_Q 0) y →
        impl.dedekindReals.Rlt (impl.dedekindReals.R_of_Q 0) z →
          impl.dedekindReals.Req
            (impl.dedekindReals.Rmult (impl.dedekindReals.Rmult x y) z)
            (impl.dedekindReals.Rmult x (impl.dedekindReals.Rmult y z))

/-- Multiplication is associative. -/
def spec_Rmult_assoc (impl : RepoImpl) : Prop :=
  ∀ (x y z : R),
    impl.dedekindReals.Req
      (impl.dedekindReals.Rmult (impl.dedekindReals.Rmult x y) z)
      (impl.dedekindReals.Rmult x (impl.dedekindReals.Rmult y z))

/-- The inverse of a positive nonzero real is positive. -/
def spec_Rinv_0_lt_compat (impl : RepoImpl) : Prop :=
  ∀ (x : R) (xNZ : impl.dedekindReals.Rneq x (impl.dedekindReals.R_of_Q 0)),
    impl.dedekindReals.Rlt (impl.dedekindReals.R_of_Q 0) x →
      impl.dedekindReals.Rlt
        (impl.dedekindReals.R_of_Q 0)
        (impl.dedekindReals.Rinv x xNZ)

/-- Inverse commutes with additive inverse. -/
def spec_Ropp_inv_permute (impl : RepoImpl) : Prop :=
  ∀ (x : R) (xNZ : impl.dedekindReals.Rneq x (impl.dedekindReals.R_of_Q 0))
      (mxNZ : impl.dedekindReals.Rneq (impl.dedekindReals.Ropp x) (impl.dedekindReals.R_of_Q 0)),
    impl.dedekindReals.Req
      (impl.dedekindReals.Ropp (impl.dedekindReals.Rinv x xNZ))
      (impl.dedekindReals.Rinv (impl.dedekindReals.Ropp x) mxNZ)

/-- The inverse is a left inverse for positive reals. -/
def spec_Rinv_l_pos (impl : RepoImpl) : Prop :=
  ∀ (x : R) (xNZ : impl.dedekindReals.Rneq x (impl.dedekindReals.R_of_Q 0)),
    impl.dedekindReals.Rlt (impl.dedekindReals.R_of_Q 0) x →
      impl.dedekindReals.Req
        (impl.dedekindReals.Rmult (impl.dedekindReals.Rinv x xNZ) x)
        (impl.dedekindReals.R_of_Q 1)

/-- The inverse is a left inverse for negative reals. -/
def spec_Rinv_l_neg (impl : RepoImpl) : Prop :=
  ∀ (x : R) (xNZ : impl.dedekindReals.Rneq x (impl.dedekindReals.R_of_Q 0)),
    impl.dedekindReals.Rlt x (impl.dedekindReals.R_of_Q 0) →
      impl.dedekindReals.Req
        (impl.dedekindReals.Rmult (impl.dedekindReals.Rinv x xNZ) x)
        (impl.dedekindReals.R_of_Q 1)

/-- The inverse is a left inverse for nonzero reals. -/
def spec_Rinv_l (impl : RepoImpl) : Prop :=
  ∀ (x : R) (xNZ : impl.dedekindReals.Rneq x (impl.dedekindReals.R_of_Q 0)),
    impl.dedekindReals.Req
      (impl.dedekindReals.Rmult (impl.dedekindReals.Rinv x xNZ) x)
      (impl.dedekindReals.R_of_Q 1)

/-- The inverse is a right inverse for nonzero reals. -/
def spec_Rinv_r (impl : RepoImpl) : Prop :=
  ∀ (x : R) (xNZ : impl.dedekindReals.Rneq x (impl.dedekindReals.R_of_Q 0)),
    impl.dedekindReals.Req
      (impl.dedekindReals.Rmult x (impl.dedekindReals.Rinv x xNZ))
      (impl.dedekindReals.R_of_Q 1)
