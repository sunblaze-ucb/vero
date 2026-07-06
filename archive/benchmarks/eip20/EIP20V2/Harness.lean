import EIP20V2.Bundle

/-!
# EIP20V2.Harness

Benchmark harness: `RepoImpl` structure, canonical implementation wiring, and
the `joint_unsat` macro consumed downstream by proof generation.

DO NOT MODIFY - benchmark infrastructure.
-/

structure RepoImpl where
  eip20 : EIP20V2Bundle

def canonical : RepoImpl where
  eip20 := {
    init := EIP20V2.init
    try_transfer := EIP20V2.try_transfer
    try_transfer_from := EIP20V2.try_transfer_from
    try_approve := EIP20V2.try_approve
    receive := EIP20V2.receive
  }

/--
`joint_unsat spec_A spec_B [spec_C ...] by <proof>` generates
```
theorem joint_unsat.spec_A.spec_B... :
    ¬ ∃ impl : RepoImpl, spec_A impl ∧ spec_B impl ∧ ... := by <proof>
```

Specs appear in the caller's order. No sorting or deduplication is performed
here; anti-cheat checks are enforced during evaluation.
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
