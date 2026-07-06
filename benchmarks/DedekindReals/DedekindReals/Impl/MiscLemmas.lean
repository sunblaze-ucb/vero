import Mathlib

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# DedekindReals.Impl.MiscLemmas

Miscellaneous rational arithmetic vocabulary translated from the Coq
`MiscLemmas` section.

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
Implement only the function bodies.
-/

-- !benchmark @start global_aux
-- !benchmark @end global_aux

namespace DedekindReals

-- ── Frozen helpers (no markers — fixed vocabulary) ─────────────

def const (A B : Type) (y : B) : A → B := fun _ => y

def power1 : Nat → Type → Type
  | 0, A => A
  | n + 1, A => power1 n A × A

def Qeq_le : Prop := ∀ p q : Rat, p = q → p ≤ q

def Qopp_lt_compat : Prop := ∀ (p q : Rat), p < q ↔ -q < -p

def Qplus_lt_lt_compat : Prop :=
  ∀ (p q r s : Rat), p < q → r < s → p + r < q + s

def Qmult_lt_positive : Prop := ∀ (p q : Rat), 0 < p → 0 < q → 0 < p * q

def Qmult_opp_r : Prop := ∀ (a b : Rat), - (a * b) = a * -b

def Qmult_opp_l : Prop := ∀ (a b : Rat), - (a * b) = -a * b

def Qlt_mult_neg_r : Prop :=
  ∀ (q r s : Rat), s < 0 → (q < r ↔ r * s < q * s)

def Qlt_mult_neg_l : Prop :=
  ∀ (q r s : Rat), q < 0 → (r < s ↔ q * s < q * r)

def Qopp_lt_shift_l : Prop := ∀ (p q : Rat), -p < q ↔ -q < p

def Qopp_lt_shift_r : Prop := ∀ (p q : Rat), p < -q ↔ q < -p

def Qlt_minus_1 : Prop := ∀ q : Rat, q + (-1 : Rat) < q

def Qlt_plus_1 : Prop := ∀ q : Rat, q < q + (1 : Rat)

def Qplus_nonneg_cone : Prop := ∀ q r : Rat, 0 ≤ q → 0 ≤ r → 0 ≤ q + r

def Qplus_zero_nonneg : Prop :=
  ∀ q r : Rat, 0 ≤ q → 0 ≤ r → q + r = 0 → q = 0 ∧ r = 0

def Qpower_zero : Prop := ∀ p : Rat, ¬ p = 0 → p ^ (0 : Nat) = 1

def Qopp_nonzero : Prop := ∀ p : Rat, ¬ p = 0 → ¬ (-p) = 0

def Qinv_gt_0_compat : Prop := ∀ a : Rat, a < 0 → a⁻¹ < 0

def Qinv_nonzero : Prop := ∀ p : Rat, ¬ p = 0 → ¬ p⁻¹ = 0

def Qpower_nonzero : Prop := ∀ (p : Rat) (n : Nat), ¬ p = 0 → ¬ p ^ n = 0

def Qpower_strictly_pos : Prop := ∀ (p : Rat) (n : Nat), 0 < p → 0 < p ^ n

def Qabs_eq_0 : Prop := ∀ q : Rat, abs q = 0 → q = 0

def Qmult_le_compat_l : Prop :=
  ∀ x y z : Rat, y ≤ z → 0 ≤ x → x * y ≤ x * z

def Qmult_le_compat : Prop :=
  ∀ q r s t : Rat, q ≤ r → 0 ≤ s → 0 ≤ q → s ≤ t → q * s ≤ r * t

def compose {A B C : Type} (g : B → C) (f : A → B) : A → C := fun x => g (f x)

end DedekindReals
