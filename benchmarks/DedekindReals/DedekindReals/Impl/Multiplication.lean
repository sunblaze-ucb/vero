import DedekindReals.Impl.Cut
import DedekindReals.Impl.Additive

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# DedekindReals.Impl.Multiplication

Multiplication and inverse for Dedekind cuts, with frozen rational-bound
vocabulary translated from the Coq `Multiplication` module.

DO NOT MODIFY types or signatures -- these are the fixed vocabulary.
Implement only the function bodies.
-/

namespace DedekindReals

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- Frozen helpers translated from the Coq multiplication development.

def Qmin4 (a b c d : Rat) : Rat := min (min a b) (min c d)

def Qmax4 (a b c d : Rat) : Rat := max (max a b) (max c d)

def mult_upper (x y : R) (q : Rat) : Prop :=
  ∃ a b c d : Rat,
    x.lower a ∧ x.upper b ∧ y.lower c ∧ y.upper d ∧
      Qmax4 (a * c) (a * d) (b * c) (b * d) < q

def mult_lower (x y : R) (q : Rat) : Prop :=
  ∃ a b c d : Rat,
    x.lower a ∧ x.upper b ∧ y.lower c ∧ y.upper d ∧
      q < Qmin4 (a * c) (a * d) (b * c) (b * d)

def Qmin4_opp : Prop :=
  ∀ a b c d : Rat, Qmin4 (-a) (-b) (-c) (-d) = -Qmax4 a b c d

def Qmax4_opp : Prop :=
  ∀ a b c d : Rat, Qmax4 (-a) (-b) (-c) (-d) = -Qmin4 a b c d

def Qpos_above_opp : Prop := ∀ q : Rat, (0 < q) ↔ (-q < q)

def Qmin4_le_max4 : Prop := ∀ a b c d : Rat, Qmin4 a b c d ≤ Qmax4 a b c d

def Qmin4_flip : Prop := ∀ a b c d : Rat, Qmin4 a b c d = Qmin4 a c b d

def Qmax4_flip : Prop := ∀ a b c d : Rat, Qmax4 a b c d = Qmax4 a c b d

def plus_max4_distr_l : Prop :=
  ∀ n m i j p : Rat, Qmax4 (p + n) (p + m) (p + i) (p + j) = p + Qmax4 n m i j

def plus_min4_distr_l : Prop :=
  ∀ n m i j p : Rat, Qmin4 (p + n) (p + m) (p + i) (p + j) = p + Qmin4 n m i j

def mult_lower_proper : Prop :=
  ∀ x y : R, ∀ q r : Rat, q = r → (mult_lower x y q ↔ mult_lower x y r)

def mult_improve_left_bound : Prop :=
  ∀ a b c d e : Rat, (c < d) → (e < b) → (a ≤ e) →
    Qmin4 (a * c) (a * d) (b * c) (b * d) ≤
      Qmin4 (e * c) (e * d) (b * c) (b * d)

def mult_improve_right_bound : Prop :=
  ∀ a b c d e : Rat, (c < d) → (a < e) → (e ≤ b) →
    Qmax4 (a * c) (a * d) (e * c) (e * d) ≤
      Qmax4 (a * c) (a * d) (b * c) (b * d)

def mult_improve_left_bound_reverse : Prop :=
  ∀ a b c d e : Rat, (c < d) → (a < e) → (e ≤ b) →
    Qmin4 (a * c) (a * d) (b * c) (b * d) ≤
      Qmin4 (a * c) (a * d) (e * c) (e * d)

def mult_improve_right_bound_reverse : Prop :=
  ∀ a b c d e : Rat, (c < d) → (e < b) → (a ≤ e) →
    Qmax4 (e * c) (e * d) (b * c) (b * d) ≤
      Qmax4 (a * c) (a * d) (b * c) (b * d)

def mult_improve_both_bounds : Prop :=
  ∀ a b c d e f : Rat, (e < f) → (c < d) → (a ≤ e) → (f ≤ b) →
    (Qmin4 (a * c) (a * d) (b * c) (b * d) ≤
        Qmin4 (e * c) (e * d) (f * c) (f * d)) ∧
      (Qmax4 (e * c) (e * d) (f * c) (f * d) ≤
        Qmax4 (a * c) (a * d) (b * c) (b * d))

def DReal_mult_disjoint : Prop :=
  ∀ (x y : R) (q : Rat), ¬ (mult_lower x y q ∧ mult_upper x y q)

def DReal_bound : Prop := ∀ x : R, ∃ q : Rat, x.upper q ∧ (Ropp x).upper q

def DReal_mult_maj_base : Prop :=
  ∀ x y p : Rat, (0 ≤ p) →
    Qmax4 0 x y (x + y + p) - Qmin4 0 x y (x + y + p) ≤ Rat.abs x + Rat.abs y + p

def DReal_mult_maj : Prop :=
  ∀ (a b e : Rat), (0 ≤ e) →
    Qmax4 (a * b) (a * (b + e)) ((a + e) * b) ((a + e) * (b + e)) -
        Qmin4 (a * b) (a * (b + e)) ((a + e) * b) ((a + e) * (b + e)) ≤
      (Rat.abs a + Rat.abs b + e) * e

def DReal_mult_located : Prop :=
  ∀ (x y : R) (q r : Rat), (q < r) → mult_lower x y q ∨ mult_upper x y r

def shrink_factor : Prop :=
  ∀ a b : Rat, a < b → ∃ q : Rat, 0 < q ∧ q < 1 ∧ a < q * b

def expand_factor : Prop :=
  ∀ a b : Rat, a < b → ∃ q : Rat, 1 < q ∧ a < q * b

def Qmul_min_distr_l : Prop :=
  ∀ n m p : Rat, 0 ≤ p → min (p * n) (p * m) = p * min n m

def split_pos : Prop :=
  ∀ x : R, ∃ a b : R, Req x (Rminus a b) ∧ Rlt (R_of_Q 0) a ∧ Rlt (R_of_Q 0) b

def inv_lower (x : R) (q : Rat) : Prop :=
  (∃ r : Rat, r < 0 ∧ x.upper r ∧ 1 < q * r) ∨
    (∃ r : Rat, x.lower 0 ∧ x.upper r ∧ q * r < 1)

def inv_upper (x : R) (q : Rat) : Prop :=
  (∃ r : Rat, x.lower r ∧ x.upper 0 ∧ q * r < 1) ∨
    (∃ r : Rat, 0 < r ∧ x.lower r ∧ 1 < q * r)

def inv_lower_pos : Prop :=
  ∀ (x : R) (q : Rat), Rlt (R_of_Q 0) x →
    (inv_lower x q ↔ (∃ r : Rat, x.upper r ∧ q * r < 1))

def inv_upper_pos : Prop :=
  ∀ (x : R) (q : Rat), Rlt (R_of_Q 0) x →
    (inv_upper x q ↔ (∃ r : Rat, 0 < r ∧ x.lower r ∧ 1 < q * r))

def inv_neg_lower_bound : Prop :=
  ∀ x : R, Rlt x (R_of_Q 0) → ∃ l : Rat, inv_lower x l

def inv_pos_lower_bound : Prop :=
  ∀ x : R, Rlt (R_of_Q 0) x → ∃ l : Rat, inv_lower x l

def inv_lower_opp : Prop :=
  ∀ (x : R) (q : Rat), inv_lower (Ropp x) q ↔ inv_upper x (-q)

def inv_upper_opp : Prop :=
  ∀ (x : R) (q : Rat), inv_upper (Ropp x) q ↔ inv_lower x (-q)

def inv_located_pos : Prop :=
  ∀ (x : R) (q r : Rat), Rlt (R_of_Q 0) x → q < r → inv_lower x q ∨ inv_upper x r

def inv_lower_proper : Prop :=
  ∀ x : R, Rneq x (R_of_Q 0) → ∀ q r : Rat, q = r → (inv_lower x q ↔ inv_lower x r)

def inv_upper_proper : Prop :=
  ∀ x : R, Rneq x (R_of_Q 0) → ∀ q r : Rat, q = r → (inv_upper x q ↔ inv_upper x r)

def inv_disjoint_pos : Prop :=
  ∀ (x : R) (q : Rat), Rlt (R_of_Q 0) x → ¬ (inv_lower x q ∧ inv_upper x q)

def inv_located : Prop :=
  ∀ (x : R) (q r : Rat), Rneq x (R_of_Q 0) → q < r → inv_lower x q ∨ inv_upper x r

def inv_lower_interval_pos : Prop :=
  ∀ (x : R) (q r : Rat), Rlt (R_of_Q 0) x → q < r → inv_lower x r → inv_lower x q

def inv_upper_interval_pos : Prop :=
  ∀ (x : R) (q r : Rat), Rlt (R_of_Q 0) x → q < r → inv_upper x q → inv_upper x r

def inv_lower_open_pos : Prop :=
  ∀ (x : R) (q : Rat), Rlt (R_of_Q 0) x →
    inv_lower x q → ∃ r : Rat, q < r ∧ inv_lower x r

def inv_upper_open_pos : Prop :=
  ∀ (x : R) (r : Rat), Rlt (R_of_Q 0) x →
    inv_upper x r → ∃ q : Rat, q < r ∧ inv_upper x q

-- API signatures

abbrev RmultSig := R → R → R
abbrev RinvSig := (x : R) → Rneq x (R_of_Q 0) → R

end DedekindReals

-- Reference implementations

-- !benchmark @start code_aux def=Rmult
-- !benchmark @end code_aux def=Rmult
namespace DedekindReals

axiom Rmult_lower_bound : ∀ x y : R, ∃ q : Rat, mult_lower x y q
axiom Rmult_upper_bound : ∀ x y : R, ∃ q : Rat, mult_upper x y q
axiom Rmult_lower_open :
  ∀ (x y : R) (q : Rat), mult_lower x y q → ∃ r : Rat, q < r ∧ mult_lower x y r
axiom Rmult_upper_open :
  ∀ (x y : R) (q : Rat), mult_upper x y q → ∃ r : Rat, r < q ∧ mult_upper x y r
axiom Rmult_disjoint : ∀ (x y : R) (q : Rat), ¬ (mult_lower x y q ∧ mult_upper x y q)
axiom Rmult_located :
  ∀ (x y : R) (q r : Rat), q < r → mult_lower x y q ∨ mult_upper x y r

end DedekindReals

def DedekindReals.Rmult : DedekindReals.RmultSig :=
-- !benchmark @start code def=Rmult
  fun x y =>
    { lower := DedekindReals.mult_lower x y
      upper := DedekindReals.mult_upper x y
      lower_proper := by
        intro q r hqr
        cases hqr
        rfl
      upper_proper := by
        intro q r hqr
        cases hqr
        rfl
      lower_bound := DedekindReals.Rmult_lower_bound x y
      upper_bound := DedekindReals.Rmult_upper_bound x y
      lower_lower := by
        intro q r hqr h
        rcases h with ⟨a, b, c, d, hxa, hxb, hyc, hyd, hbound⟩
        exact ⟨a, b, c, d, hxa, hxb, hyc, hyd, by grind⟩
      lower_open := DedekindReals.Rmult_lower_open x y
      upper_upper := by
        intro q r hqr h
        rcases h with ⟨a, b, c, d, hxa, hxb, hyc, hyd, hbound⟩
        exact ⟨a, b, c, d, hxa, hxb, hyc, hyd, by grind⟩
      upper_open := DedekindReals.Rmult_upper_open x y
      disjoint := DedekindReals.Rmult_disjoint x y
      located := DedekindReals.Rmult_located x y }
-- !benchmark @end code def=Rmult

namespace DedekindReals

def Rmult_comp : Prop :=
  ∀ x y u v : R, Req x y → Req u v → Req (Rmult x u) (Rmult y v)

end DedekindReals

-- !benchmark @start code_aux def=Rinv
-- !benchmark @end code_aux def=Rinv
namespace DedekindReals

axiom Rinv_lower_proper :
  ∀ x : R, Rneq x (R_of_Q 0) → ∀ q r : Rat, q = r → (inv_lower x q ↔ inv_lower x r)
axiom Rinv_upper_proper :
  ∀ x : R, Rneq x (R_of_Q 0) → ∀ q r : Rat, q = r → (inv_upper x q ↔ inv_upper x r)
axiom Rinv_lower_bound : ∀ x : R, Rneq x (R_of_Q 0) → ∃ q : Rat, inv_lower x q
axiom Rinv_upper_bound : ∀ x : R, Rneq x (R_of_Q 0) → ∃ q : Rat, inv_upper x q
axiom Rinv_lower_lower :
  ∀ x : R, Rneq x (R_of_Q 0) → ∀ q r : Rat, q < r → inv_lower x r → inv_lower x q
axiom Rinv_lower_open :
  ∀ x : R, Rneq x (R_of_Q 0) → ∀ q : Rat, inv_lower x q → ∃ r : Rat, q < r ∧ inv_lower x r
axiom Rinv_upper_upper :
  ∀ x : R, Rneq x (R_of_Q 0) → ∀ q r : Rat, q < r → inv_upper x q → inv_upper x r
axiom Rinv_upper_open :
  ∀ x : R, Rneq x (R_of_Q 0) → ∀ r : Rat, inv_upper x r → ∃ q : Rat, q < r ∧ inv_upper x q
axiom Rinv_disjoint :
  ∀ x : R, Rneq x (R_of_Q 0) → ∀ q : Rat, ¬ (inv_lower x q ∧ inv_upper x q)
axiom Rinv_located :
  ∀ x : R, Rneq x (R_of_Q 0) → ∀ q r : Rat, q < r → inv_lower x q ∨ inv_upper x r

end DedekindReals

def DedekindReals.Rinv : DedekindReals.RinvSig :=
-- !benchmark @start code def=Rinv
  fun x hx =>
    { lower := DedekindReals.inv_lower x
      upper := DedekindReals.inv_upper x
      lower_proper := DedekindReals.Rinv_lower_proper x hx
      upper_proper := DedekindReals.Rinv_upper_proper x hx
      lower_bound := DedekindReals.Rinv_lower_bound x hx
      upper_bound := DedekindReals.Rinv_upper_bound x hx
      lower_lower := DedekindReals.Rinv_lower_lower x hx
      lower_open := DedekindReals.Rinv_lower_open x hx
      upper_upper := DedekindReals.Rinv_upper_upper x hx
      upper_open := DedekindReals.Rinv_upper_open x hx
      disjoint := DedekindReals.Rinv_disjoint x hx
      located := DedekindReals.Rinv_located x hx }
-- !benchmark @end code def=Rinv
