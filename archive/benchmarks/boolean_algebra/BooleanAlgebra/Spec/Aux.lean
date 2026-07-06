/-!
# BooleanAlgebra.Spec.Aux

Shared auxiliary predicates for BooleanAlgebra specifications.
-/

/-- Int-encoded Boolean values used by the gate APIs. -/
def isBit (x : Int) : Prop :=
  x = 0 ∨ x = 1

