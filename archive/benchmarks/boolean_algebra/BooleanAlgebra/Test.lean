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
import BooleanAlgebra.Harness

/-!
# BooleanAlgebra.Test

Executable conformance tests. `#guard` assertions run against the
`canonical` wiring. Before the LLM sees the benchmark, the pipeline
replaces `sorry` stubs — the inventory below activates post-fill.

DO NOT MODIFY — infrastructure.
-/

-- Sentinel — proves Test.lean is wired and counts toward the validator's
-- guard tally. Real test cases live in the curator block below.
#guard True

-- Curator note: guards below were activated after Impl/*.lean stubs
-- were filled with reference implementations.
-- ── AndGate ─────────────────────────
#guard canonical.booleanAlgebra.and_gate 0 0 = 0
#guard canonical.booleanAlgebra.and_gate 0 1 = 0
#guard canonical.booleanAlgebra.and_gate 1 0 = 0
#guard canonical.booleanAlgebra.and_gate 1 1 = 1
#guard canonical.booleanAlgebra.and_gate 2 3 = 3
#guard canonical.booleanAlgebra.and_gate 5 7 = 7
#guard canonical.booleanAlgebra.and_gate 0 5 = 0
#guard canonical.booleanAlgebra.and_gate 4 0 = 0
#guard canonical.booleanAlgebra.n_input_and_gate [1, 0, 1, 1, 0] = 0
#guard canonical.booleanAlgebra.n_input_and_gate [1, 1, 1, 1, 1] = 1
#guard canonical.booleanAlgebra.n_input_and_gate [0, 0, 0, 0, 0] = 0
#guard canonical.booleanAlgebra.n_input_and_gate [1, 1, 1, 0, 1] = 0
#guard canonical.booleanAlgebra.n_input_and_gate [1] = 1
#guard canonical.booleanAlgebra.n_input_and_gate [0] = 0
#guard canonical.booleanAlgebra.n_input_and_gate [] = 1
#guard canonical.booleanAlgebra.n_input_and_gate [1, 2, 1] = 1
#guard canonical.booleanAlgebra.n_input_and_gate [1, 0, 1] = 0
#guard canonical.booleanAlgebra.n_input_and_gate [1, 0, 2] = 0

-- ── ImplyGate ─────────────────────────
#guard canonical.booleanAlgebra.imply_gate 0 0 = 1
#guard canonical.booleanAlgebra.imply_gate 0 1 = 1
#guard canonical.booleanAlgebra.imply_gate 1 0 = 0
#guard canonical.booleanAlgebra.imply_gate 1 1 = 1
#guard canonical.booleanAlgebra.recursive_imply_list [0, 0] = 1
#guard canonical.booleanAlgebra.recursive_imply_list [0, 1] = 1
#guard canonical.booleanAlgebra.recursive_imply_list [1, 0] = 0
#guard canonical.booleanAlgebra.recursive_imply_list [1, 1] = 1
#guard canonical.booleanAlgebra.recursive_imply_list [0, 0, 0] = 0
#guard canonical.booleanAlgebra.recursive_imply_list [0, 0, 1] = 1
#guard canonical.booleanAlgebra.recursive_imply_list [0, 1, 0] = 0
#guard canonical.booleanAlgebra.recursive_imply_list [0, 1, 1] = 1
#guard canonical.booleanAlgebra.recursive_imply_list [1, 0, 0] = 1
#guard canonical.booleanAlgebra.recursive_imply_list [1, 0, 1] = 1
#guard canonical.booleanAlgebra.recursive_imply_list [1, 1, 0] = 0
#guard canonical.booleanAlgebra.recursive_imply_list [1, 1, 1] = 1

-- ── KarnaughMapSimplification ─────────────────────────
#guard canonical.booleanAlgebra.simplify_kmap [[0, 1], [1, 1]] = "A'B + AB' + AB"
#guard canonical.booleanAlgebra.simplify_kmap [[0, 0], [0, 0]] = ""
#guard canonical.booleanAlgebra.simplify_kmap [[0, 1], [1, -1]] = "A'B + AB' + AB"
#guard canonical.booleanAlgebra.simplify_kmap [[0, 1], [1, 2]] = "A'B + AB' + AB"

-- ── Multiplexer ─────────────────────────
#guard canonical.booleanAlgebra.mux 0 1 0 = 0
#guard canonical.booleanAlgebra.mux 0 1 1 = 1
#guard canonical.booleanAlgebra.mux 1 0 0 = 1
#guard canonical.booleanAlgebra.mux 1 0 1 = 0
#guard canonical.booleanAlgebra.mux 0 0 0 = 0
#guard canonical.booleanAlgebra.mux 0 0 1 = 0
#guard canonical.booleanAlgebra.mux 1 1 0 = 1
#guard canonical.booleanAlgebra.mux 1 1 1 = 1

-- ── NandGate ─────────────────────────
#guard canonical.booleanAlgebra.nand_gate 0 0 = 1
#guard canonical.booleanAlgebra.nand_gate 0 1 = 1
#guard canonical.booleanAlgebra.nand_gate 1 0 = 1
#guard canonical.booleanAlgebra.nand_gate 1 1 = 0
#guard canonical.booleanAlgebra.nand_gate 5 7 = 0
#guard canonical.booleanAlgebra.nand_gate 0 5 = 1
#guard canonical.booleanAlgebra.nand_gate 2 3 = 0

-- ── NimplyGate ─────────────────────────
#guard canonical.booleanAlgebra.nimply_gate 0 0 = 0
#guard canonical.booleanAlgebra.nimply_gate 0 1 = 0
#guard canonical.booleanAlgebra.nimply_gate 1 0 = 1
#guard canonical.booleanAlgebra.nimply_gate 1 1 = 0
#guard canonical.booleanAlgebra.nimply_gate (-1) 0 = 0
#guard canonical.booleanAlgebra.nimply_gate 0 (-1) = 0
#guard canonical.booleanAlgebra.nimply_gate 2 0 = 0
#guard canonical.booleanAlgebra.nimply_gate 0 2 = 0
#guard canonical.booleanAlgebra.nimply_gate 999999999 0 = 0
#guard canonical.booleanAlgebra.nimply_gate 999999999 999999999 = 0

-- ── NorGate ─────────────────────────
#guard canonical.booleanAlgebra.nor_gate 0 0 = 1
#guard canonical.booleanAlgebra.nor_gate 0 1 = 0
#guard canonical.booleanAlgebra.nor_gate 1 0 = 0
#guard canonical.booleanAlgebra.nor_gate 1 1 = 0
#guard canonical.booleanAlgebra.nor_gate 0 (-7) = 0
#guard canonical.booleanAlgebra.truth_table canonical.booleanAlgebra.nor_gate = "Truth Table of NOR Gate:\n| Input 1  | Input 2  |  Output  |\n|    0     |    0     |    1     |\n|    0     |    1     |    0     |\n|    1     |    0     |    0     |\n|    1     |    1     |    0     |"
#guard canonical.booleanAlgebra.truth_table canonical.booleanAlgebra.or_gate = "Truth Table of NOR Gate:\n| Input 1  | Input 2  |  Output  |\n|    0     |    0     |    0     |\n|    0     |    1     |    1     |\n|    1     |    0     |    1     |\n|    1     |    1     |    1     |"
#guard canonical.booleanAlgebra.truth_table (fun _ _ => 0) = "Truth Table of NOR Gate:\n| Input 1  | Input 2  |  Output  |\n|    0     |    0     |    0     |\n|    0     |    1     |    0     |\n|    1     |    0     |    0     |\n|    1     |    1     |    0     |"

-- ── NotGate ─────────────────────────
#guard canonical.booleanAlgebra.not_gate 0 = 1
#guard canonical.booleanAlgebra.not_gate 1 = 0
#guard canonical.booleanAlgebra.not_gate (-1) = 0
#guard canonical.booleanAlgebra.not_gate 2 = 0
#guard canonical.booleanAlgebra.not_gate 100 = 0

-- ── OrGate ─────────────────────────
#guard canonical.booleanAlgebra.or_gate 0 0 = 0
#guard canonical.booleanAlgebra.or_gate 0 1 = 1
#guard canonical.booleanAlgebra.or_gate 1 0 = 1
#guard canonical.booleanAlgebra.or_gate 1 1 = 1
#guard canonical.booleanAlgebra.or_gate (-1) 0 = 0
#guard canonical.booleanAlgebra.or_gate 0 (-1) = 0
#guard canonical.booleanAlgebra.or_gate 2 1 = 1
#guard canonical.booleanAlgebra.or_gate 1 2 = 1

-- ── QuineMcCluskey ─────────────────────────
#guard canonical.booleanAlgebra.compare_string "0010" "0110" = some "0_10"
#guard canonical.booleanAlgebra.compare_string "0110" "1101" = none
#guard canonical.booleanAlgebra.compare_string "" "" = some ""
#guard canonical.booleanAlgebra.compare_string "0" "1" = some "_"
#guard canonical.booleanAlgebra.check ["0.00.01.5"] = ["0.00.01.5"]
#guard canonical.booleanAlgebra.check [] = []
#guard canonical.booleanAlgebra.check [""] = [""]
#guard canonical.booleanAlgebra.decimal_to_binary 3 [1.0, 5.0, 7.0] = ["001", "101", "111"]
#guard canonical.booleanAlgebra.decimal_to_binary 2 [] = []
#guard canonical.booleanAlgebra.decimal_to_binary 0 [0.0] = [""]
#guard canonical.booleanAlgebra.is_for_table "0010" "0110" 1 = true
#guard canonical.booleanAlgebra.is_for_table "0110" "1101" 1 = false
#guard canonical.booleanAlgebra.is_for_table "" "" 0 = true
#guard canonical.booleanAlgebra.is_for_table "0" "1" 1 = true
#guard canonical.booleanAlgebra.selection [[1, 0, 0], [0, 1, 1]] ["0_10", "1_11"] = ["0_10", "1_11"]
#guard canonical.booleanAlgebra.selection [[0]] [""] = []
#guard canonical.booleanAlgebra.selection [[1, 1], [1, 0]] ["a", "b"] = ["a"]
#guard canonical.booleanAlgebra.prime_implicant_chart [] [] = []
#guard canonical.booleanAlgebra.prime_implicant_chart [""] [""] = [[1]]
#guard canonical.booleanAlgebra.prime_implicant_chart ["0"] ["0", "1"] = [[1, 0]]

-- ── XnorGate ─────────────────────────
#guard canonical.booleanAlgebra.xnor_gate 0 0 = 1
#guard canonical.booleanAlgebra.xnor_gate 0 1 = 0
#guard canonical.booleanAlgebra.xnor_gate 1 0 = 0
#guard canonical.booleanAlgebra.xnor_gate 1 1 = 1
#guard canonical.booleanAlgebra.xnor_gate (-1) 0 = 0
#guard canonical.booleanAlgebra.xnor_gate 0 (-1) = 0
#guard canonical.booleanAlgebra.xnor_gate 2 0 = 0
#guard canonical.booleanAlgebra.xnor_gate 0 2 = 0
#guard canonical.booleanAlgebra.xnor_gate 5 5 = 1
#guard canonical.booleanAlgebra.xnor_gate 1000000 1000000 = 1

-- ── XorGate ─────────────────────────
#guard canonical.booleanAlgebra.xor_gate 0 0 = 0
#guard canonical.booleanAlgebra.xor_gate 0 1 = 1
#guard canonical.booleanAlgebra.xor_gate 1 0 = 1
#guard canonical.booleanAlgebra.xor_gate 1 1 = 0
#guard canonical.booleanAlgebra.xor_gate 5 3 = 0
#guard canonical.booleanAlgebra.xor_gate 2 2 = 0
#guard canonical.booleanAlgebra.xor_gate 0 7 = 1
#guard canonical.booleanAlgebra.xor_gate 4 0 = 1
