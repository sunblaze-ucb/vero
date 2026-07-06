import DedekindReals.Harness

/-!
# DedekindReals.Spec.MiscLemmas

Specifications for miscellaneous rational arithmetic facts. Each `spec_*`
is a property over an arbitrary `impl : RepoImpl`.

DO NOT MODIFY — this file is frozen curator-given content.
-/

open DedekindReals

/-- A nonzero nonnegative rational is strictly positive. -/
def spec_lt_from_le_nonzero (impl : RepoImpl) : Prop :=
  ∀ p : Rat, 0 ≤ p → ¬ p = 0 → 0 < p

/-- Powers of rationals at least one remain at least one. -/
def spec_pow_Q1_Qle (impl : RepoImpl) : Prop :=
  ∀ (q : Rat) (n : Nat), 1 ≤ q → 1 ≤ q ^ n

/-- Powers of rationals at least one are monotone in the exponent. -/
def spec_pow_Q1_incr (impl : RepoImpl) : Prop :=
  ∀ (q : Rat) (n p : Nat), 1 ≤ q → n ≤ p → q ^ n ≤ q ^ p

/-- The arithmetic midpoint of two rationals lies strictly between them. -/
def spec_middle_between (impl : RepoImpl) : Prop :=
  ∀ q r : Rat,
    q < r →
      q < ((q + r) * (1 / 2 : Rat)) ∧ ((q + r) * (1 / 2 : Rat)) < r
