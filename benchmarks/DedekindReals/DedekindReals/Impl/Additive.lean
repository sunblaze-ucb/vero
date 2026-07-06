import DedekindReals.Impl.Cut

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# DedekindReals.Impl.Additive

Addition, additive inverse, and subtraction for Dedekind cuts.

DO NOT MODIFY types or signatures -- these are the fixed vocabulary.
Implement only the function bodies.
-/

namespace DedekindReals

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- API signatures

abbrev RplusSig := R → R → R
abbrev RoppSig := R → R
abbrev RminusSig := R → R → R

end DedekindReals

-- Reference implementations

-- !benchmark @start code_aux def=Rplus
-- !benchmark @end code_aux def=Rplus
namespace DedekindReals

axiom Rplus_lower_bound :
  ∀ x y : R, ∃ q : Rat, ∃ r s : Rat, q < r + s ∧ x.lower r ∧ y.lower s

axiom Rplus_upper_bound :
  ∀ x y : R, ∃ q : Rat, ∃ r s : Rat, r + s < q ∧ x.upper r ∧ y.upper s

axiom Rplus_lower_open :
  ∀ (x y : R) (q : Rat),
    (∃ r s : Rat, q < r + s ∧ x.lower r ∧ y.lower s) →
      ∃ r : Rat, q < r ∧ ∃ u v : Rat, r < u + v ∧ x.lower u ∧ y.lower v

axiom Rplus_upper_open :
  ∀ (x y : R) (q : Rat),
    (∃ r s : Rat, r + s < q ∧ x.upper r ∧ y.upper s) →
      ∃ r : Rat, r < q ∧ ∃ u v : Rat, u + v < r ∧ x.upper u ∧ y.upper v

axiom Rplus_disjoint :
  ∀ (x y : R) (q : Rat),
    ¬ ((∃ r s : Rat, q < r + s ∧ x.lower r ∧ y.lower s) ∧
      (∃ r s : Rat, r + s < q ∧ x.upper r ∧ y.upper s))

axiom Rplus_located :
  ∀ (x y : R) (q r : Rat), q < r →
    (∃ u v : Rat, q < u + v ∧ x.lower u ∧ y.lower v) ∨
      (∃ u v : Rat, u + v < r ∧ x.upper u ∧ y.upper v)

end DedekindReals

def DedekindReals.Rplus : DedekindReals.RplusSig :=
-- !benchmark @start code def=Rplus
  fun x y =>
    { lower := fun q => ∃ r s : Rat, q < r + s ∧ x.lower r ∧ y.lower s
      upper := fun q => ∃ r s : Rat, r + s < q ∧ x.upper r ∧ y.upper s
      lower_proper := by
        intro q r hqr
        cases hqr
        rfl
      upper_proper := by
        intro q r hqr
        cases hqr
        rfl
      lower_bound := DedekindReals.Rplus_lower_bound x y
      upper_bound := DedekindReals.Rplus_upper_bound x y
      lower_lower := by
        intro q r hqr h
        rcases h with ⟨u, v, huv, hu, hv⟩
        exact ⟨u, v, by grind, hu, hv⟩
      lower_open := DedekindReals.Rplus_lower_open x y
      upper_upper := by
        intro q r hqr h
        rcases h with ⟨u, v, huv, hu, hv⟩
        exact ⟨u, v, by grind, hu, hv⟩
      upper_open := DedekindReals.Rplus_upper_open x y
      disjoint := DedekindReals.Rplus_disjoint x y
      located := DedekindReals.Rplus_located x y }
-- !benchmark @end code def=Rplus

-- !benchmark @start code_aux def=Ropp
-- !benchmark @end code_aux def=Ropp

def DedekindReals.Ropp : DedekindReals.RoppSig :=
-- !benchmark @start code def=Ropp
  fun x =>
    { lower := fun q => x.upper (-q)
      upper := fun q => x.lower (-q)
      lower_proper := by
        intro q r hqr
        cases hqr
        rfl
      upper_proper := by
        intro q r hqr
        cases hqr
        rfl
      lower_bound := by
        rcases x.upper_bound with ⟨r, hr⟩
        exact ⟨-r, by simpa using hr⟩
      upper_bound := by
        rcases x.lower_bound with ⟨q, hq⟩
        exact ⟨-q, by simpa using hq⟩
      lower_lower := by
        intro q r hqr hr
        exact x.upper_upper (-r) (-q) (by grind) hr
      lower_open := by
        intro q hq
        rcases x.upper_open (-q) hq with ⟨s, hslt, hs⟩
        exact ⟨-s, by grind, by simpa using hs⟩
      upper_upper := by
        intro q r hqr hq
        exact x.lower_lower (-r) (-q) (by grind) hq
      upper_open := by
        intro r hr
        rcases x.lower_open (-r) hr with ⟨q, hqlt, hq⟩
        exact ⟨-q, by grind, by simpa using hq⟩
      disjoint := by
        intro q h
        exact x.disjoint (-q) ⟨h.2, h.1⟩
      located := by
        intro q r hqr
        cases x.located (-r) (-q) (by grind) with
        | inl h => exact Or.inr (by simpa using h)
        | inr h => exact Or.inl (by simpa using h) }
-- !benchmark @end code def=Ropp

-- !benchmark @start code_aux def=Rminus
-- !benchmark @end code_aux def=Rminus

def DedekindReals.Rminus : DedekindReals.RminusSig :=
-- !benchmark @start code def=Rminus
  fun x y => DedekindReals.Rplus x (DedekindReals.Ropp y)
-- !benchmark @end code def=Rminus

namespace DedekindReals

-- Pure spec helpers.

def Rplus_comp : Prop :=
  ∀ x y u v : R, Req x y → Req u v → Req (Rplus x u) (Rplus y v)

def Ropp_comp : Prop := ∀ x y : R, Req x y → Req (Ropp x) (Ropp y)

def sum_interval_lower : Prop :=
  ∀ (x y : R) (a b : Rat), x.lower a → y.lower b → (Rplus x y).lower (a + b)

def sum_interval_upper : Prop :=
  ∀ (x y : R) (a b : Rat), x.upper a → y.upper b → (Rplus x y).upper (a + b)

end DedekindReals
