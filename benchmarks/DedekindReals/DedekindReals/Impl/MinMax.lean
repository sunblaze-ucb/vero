import DedekindReals.Impl.Cut
import DedekindReals.Impl.Additive
import DedekindReals.Impl.Multiplication

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# DedekindReals.Impl.MinMax

Minimum and maximum operations for Dedekind cuts.

DO NOT MODIFY types or signatures -- these are the fixed vocabulary.
Implement only the function bodies.
-/

namespace DedekindReals

-- Frozen helpers translated from the Coq MinMax development.

axiom unfinishedMinMax : ∀ (A : Type), A

-- API signatures

abbrev RminSig := R → R → R
abbrev RmaxSig := R → R → R

end DedekindReals

-- !benchmark @start global_aux
namespace DedekindReals

private theorem lower_le_local (x : R) {q r : Rat} :
    q ≤ r → x.lower r → x.lower q := by
  intro hqr hr
  by_cases hlt : q < r
  · exact x.lower_lower q r hlt hr
  · have heq : q = r := by grind
    cases heq
    exact hr

private theorem upper_le_local (x : R) {q r : Rat} :
    q ≤ r → x.upper q → x.upper r := by
  intro hqr hq
  by_cases hlt : q < r
  · exact x.upper_upper q r hlt hq
  · have heq : q = r := by grind
    cases heq
    exact hq

end DedekindReals
-- !benchmark @end global_aux

-- Reference implementations

-- !benchmark @start code_aux def=Rmin
-- !benchmark @end code_aux def=Rmin

def DedekindReals.Rmin : DedekindReals.RminSig :=
-- !benchmark @start code def=Rmin
  fun x y =>
    { lower := fun q => x.lower q ∧ y.lower q
      upper := fun q => x.upper q ∨ y.upper q
      lower_proper := by
        intro q r hqr
        cases hqr
        rfl
      upper_proper := by
        intro q r hqr
        cases hqr
        rfl
      lower_bound := by
        rcases x.lower_bound with ⟨q, hq⟩
        rcases y.lower_bound with ⟨r, hr⟩
        exact ⟨min q r,
          DedekindReals.lower_le_local x (by grind) hq,
          DedekindReals.lower_le_local y (by grind) hr⟩
      upper_bound := by
        rcases x.upper_bound with ⟨q, hq⟩
        exact ⟨q, Or.inl hq⟩
      lower_lower := by
        intro q r hqr h
        exact ⟨x.lower_lower q r hqr h.1, y.lower_lower q r hqr h.2⟩
      lower_open := by
        intro q h
        rcases x.lower_open q h.1 with ⟨r, hqr, hr⟩
        rcases y.lower_open q h.2 with ⟨s, hqs, hs⟩
        exact ⟨min r s, by grind,
          DedekindReals.lower_le_local x (by grind) hr,
          DedekindReals.lower_le_local y (by grind) hs⟩
      upper_upper := by
        intro q r hqr h
        cases h with
        | inl hx => exact Or.inl (x.upper_upper q r hqr hx)
        | inr hy => exact Or.inr (y.upper_upper q r hqr hy)
      upper_open := by
        intro r h
        cases h with
        | inl hx =>
            rcases x.upper_open r hx with ⟨q, hqr, hq⟩
            exact ⟨q, hqr, Or.inl hq⟩
        | inr hy =>
            rcases y.upper_open r hy with ⟨q, hqr, hq⟩
            exact ⟨q, hqr, Or.inr hq⟩
      disjoint := by
        intro q h
        rcases h with ⟨hl, hu⟩
        cases hu with
        | inl hx => exact x.disjoint q ⟨hl.1, hx⟩
        | inr hy => exact y.disjoint q ⟨hl.2, hy⟩
      located := by
        intro q r hqr
        cases x.located q r hqr with
        | inl hx =>
            cases y.located q r hqr with
            | inl hy => exact Or.inl ⟨hx, hy⟩
            | inr hy => exact Or.inr (Or.inr hy)
        | inr hx => exact Or.inr (Or.inl hx) }
-- !benchmark @end code def=Rmin

-- !benchmark @start code_aux def=Rmax
-- !benchmark @end code_aux def=Rmax

def DedekindReals.Rmax : DedekindReals.RmaxSig :=
-- !benchmark @start code def=Rmax
  fun x y =>
    { lower := fun q => x.lower q ∨ y.lower q
      upper := fun q => x.upper q ∧ y.upper q
      lower_proper := by
        intro q r hqr
        cases hqr
        rfl
      upper_proper := by
        intro q r hqr
        cases hqr
        rfl
      lower_bound := by
        rcases x.lower_bound with ⟨q, hq⟩
        exact ⟨q, Or.inl hq⟩
      upper_bound := by
        rcases x.upper_bound with ⟨q, hq⟩
        rcases y.upper_bound with ⟨r, hr⟩
        exact ⟨max q r,
          DedekindReals.upper_le_local x (by grind) hq,
          DedekindReals.upper_le_local y (by grind) hr⟩
      lower_lower := by
        intro q r hqr h
        cases h with
        | inl hx => exact Or.inl (x.lower_lower q r hqr hx)
        | inr hy => exact Or.inr (y.lower_lower q r hqr hy)
      lower_open := by
        intro q h
        cases h with
        | inl hx =>
            rcases x.lower_open q hx with ⟨r, hqr, hr⟩
            exact ⟨r, hqr, Or.inl hr⟩
        | inr hy =>
            rcases y.lower_open q hy with ⟨r, hqr, hr⟩
            exact ⟨r, hqr, Or.inr hr⟩
      upper_upper := by
        intro q r hqr h
        exact ⟨x.upper_upper q r hqr h.1, y.upper_upper q r hqr h.2⟩
      upper_open := by
        intro r h
        rcases x.upper_open r h.1 with ⟨q, hqr, hq⟩
        rcases y.upper_open r h.2 with ⟨s, hsr, hs⟩
        exact ⟨max q s, by grind,
          DedekindReals.upper_le_local x (by grind) hq,
          DedekindReals.upper_le_local y (by grind) hs⟩
      disjoint := by
        intro q h
        rcases h with ⟨hl, hu⟩
        cases hl with
        | inl hx => exact x.disjoint q ⟨hx, hu.1⟩
        | inr hy => exact y.disjoint q ⟨hy, hu.2⟩
      located := by
        intro q r hqr
        cases x.located q r hqr with
        | inl hx => exact Or.inl (Or.inl hx)
        | inr hx =>
            cases y.located q r hqr with
            | inl hy => exact Or.inl (Or.inr hy)
            | inr hy => exact Or.inr ⟨hx, hy⟩ }
-- !benchmark @end code def=Rmax
