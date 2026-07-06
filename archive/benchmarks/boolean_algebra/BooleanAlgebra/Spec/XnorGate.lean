import BooleanAlgebra.Harness
import BooleanAlgebra.Spec.Aux

/-!
# BooleanAlgebra.Spec.XnorGate

Specifications for the XNOR gate.

DO NOT MODIFY — frozen curator-given content.
-/

/-- On Int-encoded bits, XNOR returns 1 exactly when the inputs are equal. -/
def spec_xnor_gate_binary_semantics (impl : RepoImpl) : Prop :=
  ∀ a b : Int, isBit a → isBit b →
    (impl.booleanAlgebra.xnor_gate a b = 1 ↔ a = b)

/-- XNOR is NOT-XOR on Int-encoded Boolean inputs. -/
def spec_xnor_is_not_xor (impl : RepoImpl) : Prop :=
  ∀ a b : Int, isBit a → isBit b →
    impl.booleanAlgebra.xnor_gate a b =
    impl.booleanAlgebra.not_gate (impl.booleanAlgebra.xor_gate a b)

/-- Any value XNOR'd with itself is 1. -/
def spec_xnor_self (impl : RepoImpl) : Prop :=
  ∀ a : Int, impl.booleanAlgebra.xnor_gate a a = 1
