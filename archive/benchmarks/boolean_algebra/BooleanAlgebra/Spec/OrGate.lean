import BooleanAlgebra.Harness
import BooleanAlgebra.Spec.Aux

/-!
# BooleanAlgebra.Spec.OrGate

Specifications for the OR gate.

DO NOT MODIFY — frozen curator-given content.
-/

/-- On Int-encoded bits, OR returns 1 exactly when at least one input is 1. -/
def spec_or_gate_binary_semantics (impl : RepoImpl) : Prop :=
  ∀ a b : Int, isBit a → isBit b →
    (impl.booleanAlgebra.or_gate a b = 1 ↔ a = 1 ∨ b = 1)

/-- OR gate uses strict equality-to-1: returns 1 iff at least one argument is exactly 1. -/
def spec_or_gate_strict_one (impl : RepoImpl) : Prop :=
  ∀ a b : Int,
    impl.booleanAlgebra.or_gate a b =
    if a = 1 ∨ b = 1 then 1 else 0
