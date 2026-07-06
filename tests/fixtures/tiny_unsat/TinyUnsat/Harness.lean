import TinyUnsat.Bundle

/-!
# TinyUnsat.Harness — DO NOT MODIFY.

RepoImpl alias + canonical wiring + joint_unsat macro. Mirrors the
ratified bundle paradigm from reference/BankLedger/.
-/

structure RepoImpl where
  tiny : TinyUnsatBundle

def canonical : RepoImpl where
  tiny := { answer := TU.answer }

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
