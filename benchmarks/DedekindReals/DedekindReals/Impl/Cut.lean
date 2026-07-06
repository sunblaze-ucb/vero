import Init.Grind
import Init.Data.Rat.Lemmas
import Init.Grind.Ordered.Rat
import Init.Grind.Interactive

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# DedekindReals.Impl.Cut

Dedekind cuts over rational numbers, with the basic order, equality,
apartness, rational embedding, and rational constants.

DO NOT MODIFY types or signatures -- these are the fixed vocabulary.
Implement only the function bodies.
-/

namespace DedekindReals

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- Types

structure R where
  lower : Rat → Prop
  upper : Rat → Prop
  lower_proper : ∀ q r : Rat, q = r → (lower q ↔ lower r)
  upper_proper : ∀ q r : Rat, q = r → (upper q ↔ upper r)
  lower_bound : ∃ q : Rat, lower q
  upper_bound : ∃ r : Rat, upper r
  lower_lower : ∀ q r : Rat, q < r → lower r → lower q
  lower_open : ∀ q : Rat, lower q → ∃ r : Rat, q < r ∧ lower r
  upper_upper : ∀ q r : Rat, q < r → upper q → upper r
  upper_open : ∀ r : Rat, upper r → ∃ q : Rat, q < r ∧ upper q
  disjoint : ∀ q : Rat, ¬ (lower q ∧ upper q)
  located : ∀ q r : Rat, q < r → lower q ∨ upper r

-- Pure spec helpers that do not depend on forward API definitions.

def Rle_upper (x y : R) : Prop := ∀ q : Rat, y.upper q → x.upper q

def Req_upper (x y : R) : Prop := Rle_upper x y ∧ Rle_upper y x

-- API signatures

abbrev RltSig := R → R → Prop
abbrev RleSig := R → R → Prop
abbrev ReqSig := R → R → Prop
abbrev RneqSig := R → R → Prop
abbrev ROfQSig := Rat → R
abbrev RzeroSig := R
abbrev ZoneSig := R

end DedekindReals

-- Reference implementations

-- !benchmark @start code_aux def=Rlt
-- !benchmark @end code_aux def=Rlt

def DedekindReals.Rlt : DedekindReals.RltSig :=
-- !benchmark @start code def=Rlt
  fun x y => ∃ q : Rat, x.upper q ∧ y.lower q
-- !benchmark @end code def=Rlt

-- !benchmark @start code_aux def=Rle
-- !benchmark @end code_aux def=Rle

def DedekindReals.Rle : DedekindReals.RleSig :=
-- !benchmark @start code def=Rle
  fun x y => ∀ q : Rat, x.lower q → y.lower q
-- !benchmark @end code def=Rle

-- !benchmark @start code_aux def=Req
-- !benchmark @end code_aux def=Req

def DedekindReals.Req : DedekindReals.ReqSig :=
-- !benchmark @start code def=Req
  fun x y => DedekindReals.Rle x y ∧ DedekindReals.Rle y x
-- !benchmark @end code def=Req

-- !benchmark @start code_aux def=Rneq
-- !benchmark @end code_aux def=Rneq

def DedekindReals.Rneq : DedekindReals.RneqSig :=
-- !benchmark @start code def=Rneq
  fun x y => DedekindReals.Rlt x y ∨ DedekindReals.Rlt y x
-- !benchmark @end code def=Rneq

-- !benchmark @start code_aux def=R_of_Q
-- !benchmark @end code_aux def=R_of_Q

def DedekindReals.R_of_Q : DedekindReals.ROfQSig :=
-- !benchmark @start code def=R_of_Q
  fun s =>
    { lower := fun q => q < s
      upper := fun r => s < r
      lower_proper := by
        intro q r h
        cases h
        rfl
      upper_proper := by
        intro q r h
        cases h
        rfl
      lower_bound := by
        exact ⟨s - 1, by grind⟩
      upper_bound := by
        exact ⟨s + 1, by grind⟩
      lower_lower := by
        intro q r hqr hrs
        grind
      lower_open := by
        intro q hqs
        exact ⟨(q + s) / 2, by grind, by grind⟩
      upper_upper := by
        intro q r hqr hsq
        grind
      upper_open := by
        intro r hsr
        exact ⟨(s + r) / 2, by grind, by grind⟩
      disjoint := by
        intro q h
        grind
      located := by
        intro q r hqr
        by_cases hqs : q < s
        · exact Or.inl hqs
        · right
          grind }
-- !benchmark @end code def=R_of_Q

-- !benchmark @start code_aux def=Rzero
-- !benchmark @end code_aux def=Rzero

def DedekindReals.Rzero : DedekindReals.RzeroSig :=
-- !benchmark @start code def=Rzero
  DedekindReals.R_of_Q 0
-- !benchmark @end code def=Rzero

-- !benchmark @start code_aux def=Zone
-- !benchmark @end code_aux def=Zone

def DedekindReals.Zone : DedekindReals.ZoneSig :=
-- !benchmark @start code def=Zone
  DedekindReals.R_of_Q 1
-- !benchmark @end code def=Zone

namespace DedekindReals

-- Pure spec helpers that depend on the API definitions above.

def R_lower_proper : Prop :=
  ∀ (x y : R), Req x y → ∀ q r : Rat, q = r → (x.lower q ↔ y.lower r)

def R_upper_proper : Prop :=
  ∀ (x y : R), Req x y → ∀ q r : Rat, q = r → (x.upper q ↔ y.upper r)

def Equivalence_Req : Prop :=
  (∀ x : R, Req x x) ∧
    (∀ x y : R, Req x y → Req y x) ∧
      (∀ x y z : R, Req x y → Req y z → Req x z)

def Setoid_R : Prop := ∀ x y : R, Req x y ↔ Req x y

def Rlt_proper : Prop :=
  ∀ (x y z w : R), Req x y → Req z w → (Rlt x z ↔ Rlt y w)

def Rle_proper : Prop :=
  ∀ (x y z w : R), Req x y → Req z w → (Rle x z ↔ Rle y w)

def R_of_Q_proper : Prop :=
  ∀ q r : Rat, q = r → Req (R_of_Q q) (R_of_Q r)

end DedekindReals
