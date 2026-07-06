import BooleanAlgebra.Harness
import BooleanAlgebra.Spec.Aux

/-!
# BooleanAlgebra.Spec.NotGate

Specifications for the NOT gate.

DO NOT MODIFY — frozen curator-given content.
-/

/-- NOT flips Int-encoded Boolean values. -/
def spec_not_gate_binary_flip (impl : RepoImpl) : Prop :=
  ∀ a : Int, isBit a →
    (impl.booleanAlgebra.not_gate a = 1 ↔ a = 0)

/-- For binary inputs, NOT is its own inverse: `not_gate (not_gate a) = a`. -/
def spec_not_gate_involutive_binary (impl : RepoImpl) : Prop :=
  ∀ a : Int, isBit a →
    impl.booleanAlgebra.not_gate (impl.booleanAlgebra.not_gate a) = a

/-- De Morgan's law: negated AND equals OR of negated inputs on bits. -/
def spec_demorgan_and_to_or (impl : RepoImpl) : Prop :=
  ∀ a b : Int, isBit a → isBit b →
    impl.booleanAlgebra.not_gate (impl.booleanAlgebra.and_gate a b) =
    impl.booleanAlgebra.or_gate
      (impl.booleanAlgebra.not_gate a)
      (impl.booleanAlgebra.not_gate b)

/-- Dual De Morgan law: negated OR equals AND of negated inputs on bits. -/
def spec_demorgan_or_to_and (impl : RepoImpl) : Prop :=
  ∀ a b : Int, isBit a → isBit b →
    impl.booleanAlgebra.not_gate (impl.booleanAlgebra.or_gate a b) =
    impl.booleanAlgebra.and_gate
      (impl.booleanAlgebra.not_gate a)
      (impl.booleanAlgebra.not_gate b)
