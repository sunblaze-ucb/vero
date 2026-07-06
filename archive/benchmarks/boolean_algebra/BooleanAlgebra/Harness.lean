import BooleanAlgebra.Bundle

/-!
# BooleanAlgebra.Harness

Benchmark harness: `RepoImpl` structure (one field per package),
`canonical` instance wiring.

DO NOT MODIFY — this is benchmark infrastructure.
-/

structure RepoImpl where
  booleanAlgebra : BooleanAlgebraBundle

def canonical : RepoImpl where
  booleanAlgebra := {
    and_gate := BooleanAlgebra.and_gate
    n_input_and_gate := BooleanAlgebra.n_input_and_gate
    imply_gate := BooleanAlgebra.imply_gate
    recursive_imply_list := BooleanAlgebra.recursive_imply_list
    simplify_kmap := BooleanAlgebra.simplify_kmap
    mux := BooleanAlgebra.mux
    nand_gate := BooleanAlgebra.nand_gate
    nimply_gate := BooleanAlgebra.nimply_gate
    nor_gate := BooleanAlgebra.nor_gate
    truth_table := BooleanAlgebra.truth_table
    not_gate := BooleanAlgebra.not_gate
    or_gate := BooleanAlgebra.or_gate
    compare_string := BooleanAlgebra.compare_string
    check := BooleanAlgebra.check
    decimal_to_binary := BooleanAlgebra.decimal_to_binary
    is_for_table := BooleanAlgebra.is_for_table
    selection := BooleanAlgebra.selection
    prime_implicant_chart := BooleanAlgebra.prime_implicant_chart
    xnor_gate := BooleanAlgebra.xnor_gate
    xor_gate := BooleanAlgebra.xor_gate
  }
