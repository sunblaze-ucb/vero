import DedekindReals.Harness

/-!
# DedekindReals.Spec.MinMax

Specifications for minimum and maximum operations on Dedekind cuts. Each
`spec_*` is a frozen property over an arbitrary `impl : RepoImpl`.

DO NOT MODIFY -- this file is frozen curator-given content.
-/

open DedekindReals

/-- The minimum is the greatest lower bound. -/
def spec_Rmin_spec (impl : RepoImpl) : Prop :=
  ∀ (x y z : R),
    impl.dedekindReals.Rle z (impl.dedekindReals.Rmin x y) ↔
      impl.dedekindReals.Rle z x ∧ impl.dedekindReals.Rle z y

/-- The minimum is below the left operand. -/
def spec_Rmin_lower_l (impl : RepoImpl) : Prop :=
  ∀ (x y : R), impl.dedekindReals.Rle (impl.dedekindReals.Rmin x y) x

/-- The minimum is below the right operand. -/
def spec_Rmin_lower_r (impl : RepoImpl) : Prop :=
  ∀ (x y : R), impl.dedekindReals.Rle (impl.dedekindReals.Rmin x y) y

/-- Minimum is idempotent. -/
def spec_Rmin_idempotent (impl : RepoImpl) : Prop :=
  ∀ (x : R), impl.dedekindReals.Req (impl.dedekindReals.Rmin x x) x

/-- Minimum is commutative. -/
def spec_Rmin_comm (impl : RepoImpl) : Prop :=
  ∀ (x y : R),
    impl.dedekindReals.Req
      (impl.dedekindReals.Rmin x y)
      (impl.dedekindReals.Rmin y x)

/-- Minimum is associative. -/
def spec_Rmin_assoc (impl : RepoImpl) : Prop :=
  ∀ (x y z : R),
    impl.dedekindReals.Req
      (impl.dedekindReals.Rmin x (impl.dedekindReals.Rmin y z))
      (impl.dedekindReals.Rmin (impl.dedekindReals.Rmin x y) z)

/-- The maximum is the least upper bound. -/
def spec_Rmax_spec (impl : RepoImpl) : Prop :=
  ∀ (x y z : R),
    impl.dedekindReals.Rle (impl.dedekindReals.Rmax x y) z ↔
      impl.dedekindReals.Rle x z ∧ impl.dedekindReals.Rle y z

/-- The maximum is above the left operand. -/
def spec_Rmax_upper_l (impl : RepoImpl) : Prop :=
  ∀ (x y : R), impl.dedekindReals.Rle x (impl.dedekindReals.Rmax x y)

/-- The maximum is above the right operand. -/
def spec_Rmax_upper_r (impl : RepoImpl) : Prop :=
  ∀ (x y : R), impl.dedekindReals.Rle y (impl.dedekindReals.Rmax x y)

/-- Maximum is idempotent. -/
def spec_Rmax_idempotent (impl : RepoImpl) : Prop :=
  ∀ (x : R), impl.dedekindReals.Req (impl.dedekindReals.Rmax x x) x

/-- Maximum is commutative. -/
def spec_Rmax_comm (impl : RepoImpl) : Prop :=
  ∀ (x y : R),
    impl.dedekindReals.Req
      (impl.dedekindReals.Rmax x y)
      (impl.dedekindReals.Rmax y x)

/-- Maximum is associative. -/
def spec_Rmax_assoc (impl : RepoImpl) : Prop :=
  ∀ (x y z : R),
    impl.dedekindReals.Req
      (impl.dedekindReals.Rmax x (impl.dedekindReals.Rmax y z))
      (impl.dedekindReals.Rmax (impl.dedekindReals.Rmax x y) z)

/-- Minimum distributes over right addition. -/
def spec_Rmin_plus_distr_r (impl : RepoImpl) : Prop :=
  ∀ (x y z : R),
    impl.dedekindReals.Req
      (impl.dedekindReals.Rmin
        (impl.dedekindReals.Rplus x z)
        (impl.dedekindReals.Rplus y z))
      (impl.dedekindReals.Rplus (impl.dedekindReals.Rmin x y) z)

/-- Minimum distributes over left addition. -/
def spec_Rmin_plus_distr_l (impl : RepoImpl) : Prop :=
  ∀ (x y z : R),
    impl.dedekindReals.Req
      (impl.dedekindReals.Rmin
        (impl.dedekindReals.Rplus x y)
        (impl.dedekindReals.Rplus x z))
      (impl.dedekindReals.Rplus x (impl.dedekindReals.Rmin y z))

/-- Maximum distributes over right addition. -/
def spec_Rmax_plus_distr_r (impl : RepoImpl) : Prop :=
  ∀ (x y z : R),
    impl.dedekindReals.Req
      (impl.dedekindReals.Rmax
        (impl.dedekindReals.Rplus x z)
        (impl.dedekindReals.Rplus y z))
      (impl.dedekindReals.Rplus (impl.dedekindReals.Rmax x y) z)

/-- Maximum distributes over left addition. -/
def spec_Rmax_plus_distr_l (impl : RepoImpl) : Prop :=
  ∀ (x y z : R),
    impl.dedekindReals.Req
      (impl.dedekindReals.Rmax
        (impl.dedekindReals.Rplus x y)
        (impl.dedekindReals.Rplus x z))
      (impl.dedekindReals.Rplus x (impl.dedekindReals.Rmax y z))

/-- Minimum distributes over right multiplication by a positive value. -/
def spec_Rmin_mult_distr_r (impl : RepoImpl) : Prop :=
  ∀ (x y z : R),
    impl.dedekindReals.Rlt (impl.dedekindReals.R_of_Q 0) z →
      impl.dedekindReals.Req
        (impl.dedekindReals.Rmin
          (impl.dedekindReals.Rmult x z)
          (impl.dedekindReals.Rmult y z))
        (impl.dedekindReals.Rmult (impl.dedekindReals.Rmin x y) z)

/-- Minimum distributes over left multiplication by a positive value. -/
def spec_Rmin_mult_distr_l (impl : RepoImpl) : Prop :=
  ∀ (x y z : R),
    impl.dedekindReals.Rlt (impl.dedekindReals.R_of_Q 0) x →
      impl.dedekindReals.Req
        (impl.dedekindReals.Rmin
          (impl.dedekindReals.Rmult x y)
          (impl.dedekindReals.Rmult x z))
        (impl.dedekindReals.Rmult x (impl.dedekindReals.Rmin y z))

/-- Maximum distributes over right multiplication by a positive value. -/
def spec_Rmax_mult_distr_r (impl : RepoImpl) : Prop :=
  ∀ (x y z : R),
    impl.dedekindReals.Rlt (impl.dedekindReals.R_of_Q 0) z →
      impl.dedekindReals.Req
        (impl.dedekindReals.Rmax
          (impl.dedekindReals.Rmult x z)
          (impl.dedekindReals.Rmult y z))
        (impl.dedekindReals.Rmult (impl.dedekindReals.Rmax x y) z)

/-- Maximum distributes over left multiplication by a positive value. -/
def spec_Rmax_mult_distr_l (impl : RepoImpl) : Prop :=
  ∀ (x y z : R),
    impl.dedekindReals.Rlt (impl.dedekindReals.R_of_Q 0) x →
      impl.dedekindReals.Req
        (impl.dedekindReals.Rmax
          (impl.dedekindReals.Rmult x y)
          (impl.dedekindReals.Rmult x z))
        (impl.dedekindReals.Rmult x (impl.dedekindReals.Rmax y z))

/-- Negation sends minimum to maximum. -/
def spec_Ropp_min (impl : RepoImpl) : Prop :=
  ∀ (x y : R),
    impl.dedekindReals.Req
      (impl.dedekindReals.Rmin
        (impl.dedekindReals.Ropp x)
        (impl.dedekindReals.Ropp y))
      (impl.dedekindReals.Ropp (impl.dedekindReals.Rmax x y))

/-- Negation sends maximum to minimum. -/
def spec_Ropp_max (impl : RepoImpl) : Prop :=
  ∀ (x y : R),
    impl.dedekindReals.Req
      (impl.dedekindReals.Rmax
        (impl.dedekindReals.Ropp x)
        (impl.dedekindReals.Ropp y))
      (impl.dedekindReals.Ropp (impl.dedekindReals.Rmin x y))
