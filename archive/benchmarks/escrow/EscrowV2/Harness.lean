import EscrowV2.Bundle

/-!
# EscrowV2.Harness

Benchmark harness for the scoped Escrow v2 candidate.
-/

structure RepoImpl where
  escrowV2 : EscrowV2Bundle

def canonical : RepoImpl where
  escrowV2 := {
    init := Escrow.init
    receive := Escrow.receive
  }

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
