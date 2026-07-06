import BooleanAlgebra.Harness
import BooleanAlgebra.Spec.Aux

/-!
# BooleanAlgebra.Spec.XorGate

Specifications for the XOR gate.

DO NOT MODIFY — frozen curator-given content.
-/

/-- On Int-encoded bits, XOR returns 1 exactly when the inputs differ. -/
def spec_xor_gate_binary_semantics (impl : RepoImpl) : Prop :=
  ∀ a b : Int, isBit a → isBit b →
    (impl.booleanAlgebra.xor_gate a b = 1 ↔ a ≠ b)

/-- XOR of any value with itself is 0. -/
def spec_xor_gate_self_zero (impl : RepoImpl) : Prop :=
  ∀ a : Int, impl.booleanAlgebra.xor_gate a a = 0

/-- XOR of zero with any nonzero value is 1. -/
def spec_xor_gate_zero_nonzero (impl : RepoImpl) : Prop :=
  ∀ a : Int, a ≠ 0 →
    impl.booleanAlgebra.xor_gate 0 a = 1 ∧
    impl.booleanAlgebra.xor_gate a 0 = 1

/-- XOR agrees with its disjunctive-normal-form definition on bits. -/
def spec_xor_disjunctive_normal_form (impl : RepoImpl) : Prop :=
  ∀ a b : Int, isBit a → isBit b →
    impl.booleanAlgebra.xor_gate a b =
    impl.booleanAlgebra.or_gate
      (impl.booleanAlgebra.and_gate a (impl.booleanAlgebra.not_gate b))
      (impl.booleanAlgebra.and_gate (impl.booleanAlgebra.not_gate a) b)
