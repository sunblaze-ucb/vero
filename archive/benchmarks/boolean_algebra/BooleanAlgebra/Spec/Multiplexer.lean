import BooleanAlgebra.Harness
import BooleanAlgebra.Spec.Aux

/-!
# BooleanAlgebra.Spec.Multiplexer

Specifications for the multiplexer (MUX) gate.

DO NOT MODIFY — frozen curator-given content.
-/

/-- Selector 0 passes through the first data input: `mux x y 0 = x`. -/
def spec_mux_select_0 (impl : RepoImpl) : Prop :=
  ∀ x y : Int, impl.booleanAlgebra.mux x y 0 = x

/-- Selector 1 passes through the second data input: `mux x y 1 = y`. -/
def spec_mux_select_1 (impl : RepoImpl) : Prop :=
  ∀ x y : Int, impl.booleanAlgebra.mux x y 1 = y

/-- MUX gate decomposition via AND/OR/NOT for binary selector and data inputs. -/
def spec_mux_decomposition (impl : RepoImpl) : Prop :=
  ∀ s x y : Int, isBit s → isBit x → isBit y →
    impl.booleanAlgebra.mux x y s =
    impl.booleanAlgebra.or_gate
      (impl.booleanAlgebra.and_gate (impl.booleanAlgebra.not_gate s) x)
      (impl.booleanAlgebra.and_gate s y)
