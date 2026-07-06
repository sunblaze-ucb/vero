import BooleanAlgebra.Harness
import BooleanAlgebra.Spec.Aux

/-!
# BooleanAlgebra.Spec.NandGate

Specifications for the NAND gate.

DO NOT MODIFY — frozen curator-given content.
-/

/-- NAND is NOT-AND on Int-encoded Boolean inputs. -/
def spec_nand_is_not_and (impl : RepoImpl) : Prop :=
  ∀ a b : Int, isBit a → isBit b →
    impl.booleanAlgebra.nand_gate a b =
    impl.booleanAlgebra.not_gate (impl.booleanAlgebra.and_gate a b)

/-- De Morgan's first law: `nand_gate a b = or_gate (not_gate a) (not_gate b)` for binary inputs. -/
def spec_nand_demorgan (impl : RepoImpl) : Prop :=
  ∀ a b : Int, isBit a → isBit b →
    impl.booleanAlgebra.nand_gate a b =
    impl.booleanAlgebra.or_gate
      (impl.booleanAlgebra.not_gate a)
      (impl.booleanAlgebra.not_gate b)
