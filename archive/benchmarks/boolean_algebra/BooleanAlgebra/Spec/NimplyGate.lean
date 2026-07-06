import BooleanAlgebra.Harness
import BooleanAlgebra.Spec.Aux

/-!
# BooleanAlgebra.Spec.NimplyGate

Specifications for the NIMPLY (material non-implication) gate.

DO NOT MODIFY — frozen curator-given content.
-/

/-- NIMPLY uses strict equality: output is 1 iff a = 1 ∧ b = 0, for all Int inputs. -/
def spec_nimply_strict_binary (impl : RepoImpl) : Prop :=
  ∀ a b : Int,
    impl.booleanAlgebra.nimply_gate a b =
    if a = 1 ∧ b = 0 then 1 else 0

/-- For binary inputs, `nimply_gate a b = and_gate a (not_gate b)`. -/
def spec_nimply_via_and_not (impl : RepoImpl) : Prop :=
  ∀ a b : Int, isBit a → isBit b →
    impl.booleanAlgebra.nimply_gate a b =
    impl.booleanAlgebra.and_gate a (impl.booleanAlgebra.not_gate b)
