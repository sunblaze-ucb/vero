import BooleanAlgebra.Harness
import BooleanAlgebra.Spec.Aux

/-!
# BooleanAlgebra.Spec.NorGate

Specifications for the NOR gate and truth table formatter.

DO NOT MODIFY — frozen curator-given content.
-/

/-- NOR returns 1 iff both inputs are exactly 0, for all Int inputs. -/
def spec_nor_both_zero (impl : RepoImpl) : Prop :=
  ∀ a b : Int,
    impl.booleanAlgebra.nor_gate a b =
    if a = 0 ∧ b = 0 then 1 else 0

/-- De Morgan's second law: `nor_gate a b = and_gate (not_gate a) (not_gate b)` for binary inputs. -/
def spec_nor_demorgan (impl : RepoImpl) : Prop :=
  ∀ a b : Int, isBit a → isBit b →
    impl.booleanAlgebra.nor_gate a b =
    impl.booleanAlgebra.and_gate
      (impl.booleanAlgebra.not_gate a)
      (impl.booleanAlgebra.not_gate b)

/-- `truth_table` formats the supplied gate on all four Boolean input rows. -/
def spec_truth_table_nor_exact (impl : RepoImpl) : Prop :=
  ∀ gate : Int → Int → Int,
  (∀ a b : Int, isBit a → isBit b → isBit (gate a b)) →
  impl.booleanAlgebra.truth_table gate =
    "Truth Table of NOR Gate:\n" ++
    "| Input 1  | Input 2  |  Output  |\n" ++
    "|    0     |    0     |    " ++ toString (gate 0 0) ++ "     |\n" ++
    "|    0     |    1     |    " ++ toString (gate 0 1) ++ "     |\n" ++
    "|    1     |    0     |    " ++ toString (gate 1 0) ++ "     |\n" ++
    "|    1     |    1     |    " ++ toString (gate 1 1) ++ "     |"
