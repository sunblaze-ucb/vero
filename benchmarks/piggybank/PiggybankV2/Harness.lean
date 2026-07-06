import PiggybankV2.Bundle

/-!
# PiggybankV2.Harness

Benchmark harness: `RepoImpl` structure, canonical implementation
wiring, and the `joint_unsat` macro consumed by codeproof mode.

DO NOT MODIFY -- benchmark infrastructure.
-/

structure RepoImpl where
  piggybankV2 : PiggybankV2Bundle

def canonical : RepoImpl where
  piggybankV2 := {
    insert := PiggybankV2.insert
    smash := PiggybankV2.smash
    init := PiggybankV2.init
    receive := PiggybankV2.receive
  }

/--
`joint_unsat spec_A spec_B [spec_C ...] by <proof>` generates a theorem
stating that the listed specs are jointly unsatisfiable for any
`RepoImpl`.
-/
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
