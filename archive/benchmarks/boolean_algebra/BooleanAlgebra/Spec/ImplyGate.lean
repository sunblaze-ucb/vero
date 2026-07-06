import BooleanAlgebra.Harness
import BooleanAlgebra.Spec.Aux

/-!
# BooleanAlgebra.Spec.ImplyGate

Specifications for the implication gate and recursive imply list.

DO NOT MODIFY — frozen curator-given content.
-/

/-- On Int-encoded bits, implication is false exactly for true implying false. -/
def spec_imply_gate_binary_semantics (impl : RepoImpl) : Prop :=
  ∀ a b : Int, isBit a → isBit b →
    (impl.booleanAlgebra.imply_gate a b = 0 ↔ a = 1 ∧ b = 0)

/-- Reflexivity: for binary inputs, `imply_gate a a = 1`. -/
def spec_imply_gate_reflexive (impl : RepoImpl) : Prop :=
  ∀ a : Int, isBit a →
    impl.booleanAlgebra.imply_gate a a = 1

/-- `imply_gate a b = or_gate (not_gate a) b` for binary inputs. -/
def spec_imply_via_or_not (impl : RepoImpl) : Prop :=
  ∀ a b : Int, isBit a → isBit b →
    impl.booleanAlgebra.imply_gate a b =
    impl.booleanAlgebra.or_gate (impl.booleanAlgebra.not_gate a) b

/-- The two-element recursive imply list reduces to a single `imply_gate`. -/
def spec_recursive_imply_list_two (impl : RepoImpl) : Prop :=
  ∀ a b : Int,
    impl.booleanAlgebra.recursive_imply_list [a, b] =
    impl.booleanAlgebra.imply_gate a b

/-- Three-element recursive imply list is a left-fold: `[a,b,c] = imply(imply(a,b),c)`. -/
def spec_recursive_imply_list_associativity (impl : RepoImpl) : Prop :=
  ∀ a b c : Int, isBit a → isBit b → isBit c →
    impl.booleanAlgebra.recursive_imply_list [a, b, c] =
    impl.booleanAlgebra.imply_gate
      (impl.booleanAlgebra.imply_gate a b) c
