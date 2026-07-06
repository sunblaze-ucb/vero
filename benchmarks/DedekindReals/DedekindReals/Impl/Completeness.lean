import DedekindReals.Impl.Cut

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# DedekindReals.Impl.Completeness

Dedekind completeness for cuts over the previously defined real numbers.

DO NOT MODIFY types or signatures -- these are the fixed vocabulary.
Implement only the function bodies.
-/

namespace DedekindReals

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- Types

structure RCut where
  r_lower : R → Prop
  r_upper : R → Prop
  r_lower_proper : ∀ x y : R, Req x y → (r_lower x ↔ r_lower y)
  r_upper_proper : ∀ x y : R, Req x y → (r_upper x ↔ r_upper y)
  r_lower_bound : ∃ x : R, r_lower x
  r_upper_bound : ∃ x : R, r_upper x
  r_lower_lower : ∀ x y : R, Rlt x y → r_lower y → r_lower x
  r_lower_open : ∀ x : R, r_lower x → ∃ y : R, Rlt x y ∧ r_lower y
  r_upper_upper : ∀ x y : R, Rlt x y → r_upper x → r_upper y
  r_upper_open : ∀ y : R, r_upper y → ∃ x : R, Rlt x y ∧ r_upper x
  r_disjoint : ∀ x : R, ¬ (r_lower x ∧ r_upper x)
  r_located : ∀ x y : R, Rlt x y → r_lower x ∨ r_upper y

-- Pure spec helpers.

def RCut_eq (c d : RCut) : Prop :=
  (∀ x : R, c.r_lower x ↔ d.r_lower x) ∧
    (∀ x : R, c.r_upper x ↔ d.r_upper x)

-- API signatures

abbrev RCutOfRSig := R → RCut
abbrev ROfRCutSig := RCut → R

end DedekindReals

-- Reference implementations

-- !benchmark @start code_aux def=RCut_of_R
namespace DedekindReals

private theorem lower_below_upper_local (x : R) (q r : Rat) :
    x.lower q → x.upper r → q < r := by
  intro hq hr
  by_cases hqr : q < r
  · exact hqr
  · exfalso
    have huq : x.upper q := by
      by_cases hrltq : r < q
      · exact x.upper_upper r q hrltq hr
      · have hqe : q = r := by grind
        exact (x.upper_proper r q hqe.symm).mp hr
    exact x.disjoint q ⟨hq, huq⟩

private theorem Rlt_trans_local (x y z : R) :
    Rlt x y → Rlt y z → Rlt x z := by
  intro hxy hyz
  rcases hxy with ⟨q, hxq, hyq⟩
  rcases hyz with ⟨r, hyr, hzr⟩
  exact ⟨q, hxq, z.lower_lower q r (lower_below_upper_local y q r hyq hyr) hzr⟩

private theorem Rlt_irrefl_local (x : R) : ¬ Rlt x x := by
  intro h
  rcases h with ⟨q, hu, hl⟩
  exact x.disjoint q ⟨hl, hu⟩

private theorem Rlt_asymm_local (x y : R) : ¬ (Rlt x y ∧ Rlt y x) := by
  intro h
  exact Rlt_irrefl_local x (Rlt_trans_local x y x h.1 h.2)

private theorem Rlt_linear_local (x y z : R) :
    Rlt x y → Rlt x z ∨ Rlt z y := by
  intro hxy
  rcases hxy with ⟨q, hxq, hyq⟩
  rcases x.upper_open q hxq with ⟨s, hsq, hxs⟩
  cases z.located s q hsq with
  | inl hzs => exact Or.inl ⟨s, hxs, hzs⟩
  | inr hzq => exact Or.inr ⟨q, hzq, hyq⟩

private theorem Rle_equiv_local (x y : R) :
    Rle x y ↔ Rle_upper x y := by
  constructor
  · intro hxy q hyq
    rcases y.upper_open q hyq with ⟨r, hrq, hyr⟩
    cases x.located r q hrq with
    | inl hxr =>
        have hyr_lower : y.lower r := hxy r hxr
        exact False.elim (y.disjoint r ⟨hyr_lower, hyr⟩)
    | inr hxq => exact hxq
  · intro hxy q hxq
    rcases x.lower_open q hxq with ⟨r, hqr, hxr⟩
    cases y.located q r hqr with
    | inl hyq => exact hyq
    | inr hyr =>
        have hxu : x.upper r := hxy r hyr
        exact False.elim (x.disjoint r ⟨hxr, hxu⟩)

private theorem R_upper_proper_local (x y : R) :
    Req x y → ∀ q : Rat, x.upper q ↔ y.upper q := by
  intro hxy q
  constructor
  · intro hxq
    exact (Rle_equiv_local y x).mp hxy.2 q hxq
  · intro hyq
    exact (Rle_equiv_local x y).mp hxy.1 q hyq

private theorem R_lower_proper_local (x y : R) :
    Req x y → ∀ q : Rat, x.lower q ↔ y.lower q := by
  intro hxy q
  exact ⟨fun hxq => hxy.1 q hxq, fun hyq => hxy.2 q hyq⟩

private theorem Rlt_proper_local (x y z w : R) :
    Req x y → Req z w → (Rlt x z ↔ Rlt y w) := by
  intro hxy hzw
  constructor
  · intro hxz
    rcases hxz with ⟨q, hxq, hzq⟩
    exact ⟨q, (R_upper_proper_local x y hxy q).mp hxq,
      (R_lower_proper_local z w hzw q).mp hzq⟩
  · intro hyw
    rcases hyw with ⟨q, hyq, hwq⟩
    exact ⟨q, (R_upper_proper_local x y hxy q).mpr hyq,
      (R_lower_proper_local z w hzw q).mpr hwq⟩

end DedekindReals
-- !benchmark @end code_aux def=RCut_of_R

def DedekindReals.RCut_of_R : DedekindReals.RCutOfRSig :=
-- !benchmark @start code def=RCut_of_R
  fun x =>
    { r_lower := fun y => DedekindReals.Rlt y x
      r_upper := fun z => DedekindReals.Rlt x z
      r_lower_proper := by
        intro u v huv
        exact DedekindReals.Rlt_proper_local u v x x huv ⟨fun q hq => hq, fun q hq => hq⟩
      r_upper_proper := by
        intro u v huv
        exact DedekindReals.Rlt_proper_local x x u v ⟨fun q hq => hq, fun q hq => hq⟩ huv
      r_lower_bound := by
        rcases x.lower_bound with ⟨q, hxq⟩
        rcases x.lower_open q hxq with ⟨r, hqr, hxr⟩
        exact ⟨DedekindReals.R_of_Q q, ⟨r, by dsimp [DedekindReals.R_of_Q]; exact hqr, hxr⟩⟩
      r_upper_bound := by
        rcases x.upper_bound with ⟨q, hxq⟩
        rcases x.upper_open q hxq with ⟨r, hrq, hxr⟩
        exact ⟨DedekindReals.R_of_Q q, ⟨r, hxr, by dsimp [DedekindReals.R_of_Q]; exact hrq⟩⟩
      r_lower_lower := by
        intro a b hab hbx
        exact DedekindReals.Rlt_trans_local a b x hab hbx
      r_lower_open := by
        intro z hzx
        rcases hzx with ⟨q, hzq, hxq⟩
        rcases z.upper_open q hzq with ⟨r, hrq, hzr⟩
        rcases x.lower_open q hxq with ⟨s, hqs, hxs⟩
        exact ⟨DedekindReals.R_of_Q q,
          ⟨⟨r, hzr, by dsimp [DedekindReals.R_of_Q]; exact hrq⟩,
            ⟨s, by dsimp [DedekindReals.R_of_Q]; exact hqs, hxs⟩⟩⟩
      r_upper_upper := by
        intro a b hab hxa
        exact DedekindReals.Rlt_trans_local x a b hxa hab
      r_upper_open := by
        intro y hxy
        rcases hxy with ⟨q, hxq, hyq⟩
        rcases x.upper_open q hxq with ⟨r, hrq, hxr⟩
        rcases y.lower_open q hyq with ⟨s, hqs, hys⟩
        exact ⟨DedekindReals.R_of_Q q,
          ⟨⟨s, by dsimp [DedekindReals.R_of_Q]; exact hqs, hys⟩,
            ⟨r, hxr, by dsimp [DedekindReals.R_of_Q]; exact hrq⟩⟩⟩
      r_disjoint := by
        intro y h
        exact DedekindReals.Rlt_asymm_local y x h
      r_located := by
        intro y z hyz
        exact DedekindReals.Rlt_linear_local y z x hyz }
-- !benchmark @end code def=RCut_of_R

-- !benchmark @start code_aux def=R_of_RCut
-- !benchmark @end code_aux def=R_of_RCut

def DedekindReals.R_of_RCut : DedekindReals.ROfRCutSig :=
-- !benchmark @start code def=R_of_RCut
  fun c =>
    { lower := fun q => ∃ x : DedekindReals.R, c.r_lower x ∧ x.lower q
      upper := fun q => ∃ y : DedekindReals.R, c.r_upper y ∧ y.upper q
      lower_proper := by
        intro q r hqr
        cases hqr
        rfl
      upper_proper := by
        intro q r hqr
        cases hqr
        rfl
      lower_bound := by
        rcases c.r_lower_bound with ⟨x, hx⟩
        rcases x.lower_bound with ⟨q, hq⟩
        exact ⟨q, x, hx, hq⟩
      upper_bound := by
        rcases c.r_upper_bound with ⟨x, hx⟩
        rcases x.upper_bound with ⟨q, hq⟩
        exact ⟨q, x, hx, hq⟩
      lower_lower := by
        intro q r hqr h
        rcases h with ⟨x, hx, hxr⟩
        exact ⟨x, hx, x.lower_lower q r hqr hxr⟩
      lower_open := by
        intro q h
        rcases h with ⟨x, hx, hxq⟩
        rcases x.lower_open q hxq with ⟨r, hqr, hxr⟩
        exact ⟨r, hqr, x, hx, hxr⟩
      upper_upper := by
        intro q r hqr h
        rcases h with ⟨x, hx, hxq⟩
        exact ⟨x, hx, x.upper_upper q r hqr hxq⟩
      upper_open := by
        intro r h
        rcases h with ⟨y, hy, hyr⟩
        rcases y.upper_open r hyr with ⟨q, hqr, hyq⟩
        exact ⟨q, hqr, y, hy, hyq⟩
      disjoint := by
        intro q h
        rcases h.1 with ⟨x, hcx, hxq⟩
        rcases h.2 with ⟨y, hcy, hyq⟩
        have hyx : DedekindReals.Rlt y x := ⟨q, hyq, hxq⟩
        have hcx_upper : c.r_upper x := c.r_upper_upper y x hyx hcy
        exact c.r_disjoint x ⟨hcx, hcx_upper⟩
      located := by
        intro q r hqr
        let a : Rat := (q + q + r) / 3
        let b : Rat := (q + r + r) / 3
        have hqa : q < a := by
          dsimp [a]
          grind
        have hbr : b < r := by
          dsimp [b]
          grind
        have hab : DedekindReals.Rlt (DedekindReals.R_of_Q a) (DedekindReals.R_of_Q b) := by
          exact ⟨(q + r) / 2,
            by
              dsimp [DedekindReals.R_of_Q, a]
              grind,
            by
              dsimp [DedekindReals.R_of_Q, b]
              grind⟩
        cases c.r_located (DedekindReals.R_of_Q a) (DedekindReals.R_of_Q b) hab with
        | inl hca =>
            exact Or.inl ⟨DedekindReals.R_of_Q a, hca,
              by
                dsimp [DedekindReals.R_of_Q]
                exact hqa⟩
        | inr hcb =>
            exact Or.inr ⟨DedekindReals.R_of_Q b, hcb,
              by
                dsimp [DedekindReals.R_of_Q]
                exact hbr⟩ }
-- !benchmark @end code def=R_of_RCut
