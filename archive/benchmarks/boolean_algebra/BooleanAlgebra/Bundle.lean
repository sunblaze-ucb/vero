import BooleanAlgebra.Impl.AndGate
import BooleanAlgebra.Impl.ImplyGate
import BooleanAlgebra.Impl.KarnaughMapSimplification
import BooleanAlgebra.Impl.Multiplexer
import BooleanAlgebra.Impl.NandGate
import BooleanAlgebra.Impl.NimplyGate
import BooleanAlgebra.Impl.NorGate
import BooleanAlgebra.Impl.NotGate
import BooleanAlgebra.Impl.OrGate
import BooleanAlgebra.Impl.QuineMcCluskey
import BooleanAlgebra.Impl.XnorGate
import BooleanAlgebra.Impl.XorGate

/-!
# BooleanAlgebra.Bundle

Per-package implementation bundle. Collects all API signatures into
one `structure BooleanAlgebraBundle`.

DO NOT MODIFY — benchmark infrastructure.
-/

structure BooleanAlgebraBundle where
  and_gate : BooleanAlgebra.AndGateSig
  n_input_and_gate : BooleanAlgebra.NInputAndGateSig
  imply_gate : BooleanAlgebra.ImplyGateSig
  recursive_imply_list : BooleanAlgebra.RecursiveImplyListSig
  simplify_kmap : BooleanAlgebra.SimplifyKmapSig
  mux : BooleanAlgebra.MuxSig
  nand_gate : BooleanAlgebra.NandGateSig
  nimply_gate : BooleanAlgebra.NimplyGateSig
  nor_gate : BooleanAlgebra.NorGateSig
  truth_table : BooleanAlgebra.TruthTableSig
  not_gate : BooleanAlgebra.NotGateSig
  or_gate : BooleanAlgebra.OrGateSig
  compare_string : BooleanAlgebra.CompareStringSig
  check : BooleanAlgebra.CheckSig
  decimal_to_binary : BooleanAlgebra.DecimalToBinarySig
  is_for_table : BooleanAlgebra.IsForTableSig
  selection : BooleanAlgebra.SelectionSig
  prime_implicant_chart : BooleanAlgebra.PrimeImplicantChartSig
  xnor_gate : BooleanAlgebra.XnorGateSig
  xor_gate : BooleanAlgebra.XorGateSig
