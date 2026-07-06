import DedekindReals.Harness

/-!
# DedekindReals.Spec.Additive

Specifications for additive operations on Dedekind cuts. Each `spec_*` is a
frozen property over an arbitrary `impl : RepoImpl`.

DO NOT MODIFY -- this file is frozen curator-given content.
-/

open DedekindReals

/-- Addition of Dedekind reals is associative. -/
def spec_Rplus_assoc (impl : RepoImpl) : Prop :=
  ∀ (x y z : R),
    impl.dedekindReals.Req
      (impl.dedekindReals.Rplus (impl.dedekindReals.Rplus x y) z)
      (impl.dedekindReals.Rplus x (impl.dedekindReals.Rplus y z))

/-- Addition of Dedekind reals is commutative. -/
def spec_Rplus_comm (impl : RepoImpl) : Prop :=
  ∀ (x y : R),
    impl.dedekindReals.Req
      (impl.dedekindReals.Rplus x y)
      (impl.dedekindReals.Rplus y x)

/-- Zero is a left identity for addition. -/
def spec_Rplus_0_l (impl : RepoImpl) : Prop :=
  ∀ (x : R),
    impl.dedekindReals.Req
      (impl.dedekindReals.Rplus (impl.dedekindReals.R_of_Q 0) x)
      x

/-- Zero is a right identity for addition. -/
def spec_Rplus_0_r (impl : RepoImpl) : Prop :=
  ∀ (x : R),
    impl.dedekindReals.Req
      (impl.dedekindReals.Rplus x (impl.dedekindReals.R_of_Q 0))
      x

/-- Additive inverse is involutive. -/
def spec_Ropp_involutive (impl : RepoImpl) : Prop :=
  ∀ (x : R),
    impl.dedekindReals.Req
      (impl.dedekindReals.Ropp (impl.dedekindReals.Ropp x))
      x

/-- Adding the right inverse gives zero. -/
def spec_Rplus_opp_r (impl : RepoImpl) : Prop :=
  ∀ (x : R),
    impl.dedekindReals.Req
      (impl.dedekindReals.Rplus x (impl.dedekindReals.Ropp x))
      (impl.dedekindReals.R_of_Q 0)

/-- Adding the left inverse gives zero. -/
def spec_Rplus_opp_l (impl : RepoImpl) : Prop :=
  ∀ (x : R),
    impl.dedekindReals.Req
      (impl.dedekindReals.Rplus (impl.dedekindReals.Ropp x) x)
      (impl.dedekindReals.R_of_Q 0)

/-- Negation distributes over addition. -/
def spec_Ropp_plus_distr (impl : RepoImpl) : Prop :=
  ∀ (r1 r2 : R),
    impl.dedekindReals.Req
      (impl.dedekindReals.Ropp (impl.dedekindReals.Rplus r1 r2))
      (impl.dedekindReals.Rplus
        (impl.dedekindReals.Ropp r1)
        (impl.dedekindReals.Ropp r2))

/-- Strict order can be cancelled on the left of addition. -/
def spec_Rplus_lt_reg_l (impl : RepoImpl) : Prop :=
  ∀ (r r1 r2 : R),
    impl.dedekindReals.Rlt
        (impl.dedekindReals.Rplus r r1)
        (impl.dedekindReals.Rplus r r2) →
      impl.dedekindReals.Rlt r1 r2

/-- Strict order can be cancelled on the right of addition. -/
def spec_Rplus_lt_reg_r (impl : RepoImpl) : Prop :=
  ∀ (r r1 r2 : R),
    impl.dedekindReals.Rlt
        (impl.dedekindReals.Rplus r1 r)
        (impl.dedekindReals.Rplus r2 r) →
      impl.dedekindReals.Rlt r1 r2

/-- Non-strict order is compatible with adding the same value on the left. -/
def spec_Rplus_le_compat_l (impl : RepoImpl) : Prop :=
  ∀ (x y z : R),
    impl.dedekindReals.Rle y z ↔
      impl.dedekindReals.Rle
        (impl.dedekindReals.Rplus x y)
        (impl.dedekindReals.Rplus x z)

/-- Non-strict order is compatible with adding the same value on the right. -/
def spec_Rplus_le_compat_r (impl : RepoImpl) : Prop :=
  ∀ (x y z : R),
    impl.dedekindReals.Rle x y ↔
      impl.dedekindReals.Rle
        (impl.dedekindReals.Rplus x z)
        (impl.dedekindReals.Rplus y z)

/-- Rational embedding preserves addition. -/
def spec_R_of_Q_plus (impl : RepoImpl) : Prop :=
  ∀ (q r : Rat),
    impl.dedekindReals.Req
      (impl.dedekindReals.R_of_Q (q + r))
      (impl.dedekindReals.Rplus
        (impl.dedekindReals.R_of_Q q)
        (impl.dedekindReals.R_of_Q r))
