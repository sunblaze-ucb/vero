import BankLedger.Harness
import BankLedger.Spec.Account
import BankLedger.Spec.Transaction
import BankLedger.Spec.Transfer
import BankLedger.Spec.Ledger

-- !benchmark @start imports

-- !benchmark @end imports

/-!
# BankLedger.Proof_modecodeproof.Joint (illustration — `codeproof` mode)

Workspace for the single joint-unsatisfiability claim per benchmark.
One slot, named `joint_unsatisfiability`. Paired with `sat_S` theorems
in `Proof_modecodeproof/<Module>.lean` files: a spec S named in the
`!solution` below must also have its `sat_S` body proved.

Multi-crate note: regardless of crate count, there is exactly ONE
`Joint.lean` and ONE joint slot per benchmark. Specs from any crate
can appear in the `!solution` list (use fully qualified names if
crates namespace their specs).

## Instructions for the LLM

If you identify a set of ≥ 2 specs that are jointly unsatisfiable
(none of them individually unsat — otherwise use `unsat_S` in the
per-module file instead):

1. Edit the `!solution` block — replace the placeholder list with your
   chosen spec names in `[]` notation, e.g.
   `specs=[spec_create_exists, spec_close_removes]`.
2. Uncomment and fill the `claim` marker so the file compiles locally,
   e.g. replace `-- joint_unsat <specs> by` with
   `joint_unsat spec_create_exists spec_close_removes by`. Use the SAME
   order as in `!solution`.
3. Uncomment the `sorry` inside the `proof` marker and replace it with
   your tactic proof body.
4. If you need helper definitions (lemmas, local defs) for the proof,
   put them inside the `proof_aux` marker — it sits at file-level,
   BEFORE the `claim`, so defs there live outside the theorem.

If you do not wish to claim any joint-unsat, leave all blocks
commented / unfilled; the file remains compile-clean.

## What the evaluator does

- Reads the spec list from `!solution`. Duplicates are rejected
  (no faked arity).
- Reads the tactic body from `!benchmark proof`.
- Rerenders the macro invocation from the spec list + body:
  `joint_unsat <specs> by <body>`. Your own `claim` content is
  discarded and never reaches evaluation.

## Example (for reference only)

```
-- !benchmark @start imports
-- (LLM may add imports here, e.g. Mathlib.Tactic)
-- !benchmark @end imports

-- !benchmark @start global_aux
-- (file-level helper defs available to all slots)
-- !benchmark @end global_aux

-- !solution @start def=joint_unsatisfiability kind=joint_unsat
-- specs=[spec_create_exists, spec_close_removes]
-- !solution @end def=joint_unsatisfiability kind=joint_unsat

-- !benchmark @start proof_aux def=joint_unsatisfiability
-- (helper defs for this proof, file-level — BEFORE the macro call)
-- !benchmark @end proof_aux def=joint_unsatisfiability

-- !benchmark @start claim def=joint_unsatisfiability kind=joint_unsat
joint_unsat spec_create_exists spec_close_removes by
-- !benchmark @end claim def=joint_unsatisfiability

-- !benchmark @start proof def=joint_unsatisfiability kind=joint_unsat
  intro ⟨impl, h1, h2⟩
  -- derive contradiction from h1 and h2
  sorry
-- !benchmark @end proof def=joint_unsatisfiability
```
-/


-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- ── The one joint-unsat slot ─────────────────────────────────

-- !solution @start def=joint_unsatisfiability kind=joint_unsat
-- specs=[<FILL: comma-separated spec names, e.g. spec_a, spec_b>]
-- !solution @end def=joint_unsatisfiability kind=joint_unsat

-- !benchmark @start proof_aux def=joint_unsatisfiability
-- !benchmark @end proof_aux def=joint_unsatisfiability

-- !benchmark @start claim def=joint_unsatisfiability kind=joint_unsat
-- joint_unsat <specs> by
-- !benchmark @end claim def=joint_unsatisfiability

-- !benchmark @start proof def=joint_unsatisfiability kind=joint_unsat
-- sorry
-- !benchmark @end proof def=joint_unsatisfiability
