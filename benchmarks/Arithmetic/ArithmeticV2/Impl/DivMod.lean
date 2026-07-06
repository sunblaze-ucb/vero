import ArithmeticV2.Impl.Internals.DivInternals
import ArithmeticV2.Impl.Internals.ModInternals

/-!
# ArithmeticV2.Impl.DivMod

Division and modulo helper vocabulary translated from Verus `div_mod.rs`.
This module has no scored executable APIs; the definitions here are frozen
vocabulary used by translated specifications.
-/


namespace ArithmeticV2

/--
This function says that `x` is congruent to `y` modulo `m` if and only if their
difference `x - y` is congruent to 0 modulo `m`.
-/
def is_mod_equivalent (x y m : Int) : Prop := x % m = y % m ↔ (x - y) % m = 0

/-- Selected source item for the division basics broadcast group. -/
def group_div_basics : Prop := True

/-- Selected source item for the modulo basics broadcast group. -/
def group_mod_basics : Prop := True

/-- Selected source item for the modulo properties broadcast group. -/
def group_mod_properties : Prop := True

/-- Selected source item for the converse fundamental div/mod broadcast group. -/
def group_fundamental_div_mod_converse : Prop := True

/--
This proof is not exported from this module. It is used only in the proof of
`lemma_fundamental_div_mod_converse`.
-/
def helper_lemma_fundamental_div_mod_converse_helper_1 : Prop :=
  ∀ (u : Int) (d : Int) (r : Int), d ≠ 0 ∧ (0 ≤ r ∧ r < d) → u = (u * d + r) / d

/--
This proof is not exported from this module. It is used only in the proof of
`lemma_fundamental_div_mod_converse`.
-/
def helper_lemma_fundamental_div_mod_converse_helper_2 : Prop :=
  ∀ (u : Int) (d : Int) (r : Int), d ≠ 0 ∧ (0 ≤ r ∧ r < d) → r = (u * d + r) % d

end ArithmeticV2
