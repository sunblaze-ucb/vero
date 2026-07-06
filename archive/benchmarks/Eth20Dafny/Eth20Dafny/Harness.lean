import Eth20Dafny.Bundle

/-!
# Eth20Dafny.Harness

Benchmark harness with RepoImpl, canonical implementation, and the
joint_unsat macro consumed by codeproof-mode proof files.
*-/

structure RepoImpl where
  eth2Dafny : Eth20DafnyBundle

def canonical : RepoImpl where
  eth2Dafny := {
    largestIndexOfOne := Eth20Dafny.largestIndexOfOne
    fromBitlistToBytes := Eth20Dafny.fromBitlistToBytes
    fromBytesToBitList := Eth20Dafny.fromBytesToBitList
    fromBitvectorToBytes := Eth20Dafny.fromBitvectorToBytes
    fromBytesToBitVector := Eth20Dafny.fromBytesToBitVector
    boolToBytes := Eth20Dafny.boolToBytes
    boolSeDesByteToBool := Eth20Dafny.boolSeDesByteToBool
    boolToByte := Eth20Dafny.boolToByte
    bytesAndBitsByteToBool := Eth20Dafny.bytesAndBitsByteToBool
    list8BitsToByte := Eth20Dafny.list8BitsToByte
    byteTo8Bits := Eth20Dafny.byteTo8Bits
    fromBitsToBytes := Eth20Dafny.fromBitsToBytes
    uintSe := Eth20Dafny.uintSe
    uintDes := Eth20Dafny.uintDes
    sizeOf := Eth20Dafny.sizeOf
    default := Eth20Dafny.default
    serialise := Eth20Dafny.serialise
    serialiseSeqOfBasics := Eth20Dafny.serialiseSeqOfBasics
    deserialise := Eth20Dafny.deserialise
    get_next_power_of_two := Eth20Dafny.get_next_power_of_two
    get_prev_power_of_two := Eth20Dafny.get_prev_power_of_two
  }

-- joint_unsat macro
syntax "joint_unsat" ident ident ident* "by" tacticSeq : command

open Lean in
macro_rules
  | `(joint_unsat $s1 $s2 $[$rest]* by $proof) => do
    let specs := #[s1, s2] ++ rest
    let name := specs.foldl (init := `joint_unsat) fun acc s => Name.append acc s.getId
    let mut body ← `($(specs[0]!) impl)
    for s in specs[1:] do
      body ← `($body ∧ $s impl)
    `(theorem $(mkIdent name) : ¬ ∃ impl : RepoImpl, $body := by $proof)
