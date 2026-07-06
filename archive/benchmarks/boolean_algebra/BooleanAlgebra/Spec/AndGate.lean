import BooleanAlgebra.Harness
import BooleanAlgebra.Spec.Aux

/-!
# BooleanAlgebra.Spec.AndGate

Specifications for the AND gate and N-input AND gate.

DO NOT MODIFY — frozen curator-given content.
-/

/-- On Int-encoded bits, AND returns 1 exactly when both inputs are 1. -/
def spec_and_gate_binary_semantics (impl : RepoImpl) : Prop :=
  ∀ a b : Int, isBit a → isBit b →
    (impl.booleanAlgebra.and_gate a b = 1 ↔ a = 1 ∧ b = 1)

/-- Zero is the absorbing element: `and_gate 0 b = 0` for all b : Int. -/
def spec_and_gate_zero_absorb (impl : RepoImpl) : Prop :=
  ∀ b : Int, impl.booleanAlgebra.and_gate 0 b = 0

/-- The n-input AND of the empty list is the identity element 1. -/
def spec_n_input_and_gate_empty (impl : RepoImpl) : Prop :=
  ∀ xs : List Int,
    xs = [] →
    impl.booleanAlgebra.n_input_and_gate xs = 1

/-- The n-input AND of a singleton list is the element itself. -/
def spec_n_input_and_gate_singleton (impl : RepoImpl) : Prop :=
  ∀ a : Int, isBit a →
    impl.booleanAlgebra.n_input_and_gate [a] = a

/-- The 2-element n-input AND agrees with the binary AND gate. -/
def spec_n_input_and_gate_vs_and (impl : RepoImpl) : Prop :=
  ∀ a b : Int, isBit a → isBit b →
    impl.booleanAlgebra.n_input_and_gate [a, b] =
    impl.booleanAlgebra.and_gate a b
