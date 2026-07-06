import DepositSc.Bundle

/-!
# DepositSc.Harness

Benchmark harness: `RepoImpl` (one field per package), `canonical`
wiring to the `Impl/` stubs, and the standard `joint_unsat` macro.

DO NOT MODIFY — benchmark infrastructure.
-/

-- ── Implementation bundle (one field per package) ───────────

structure RepoImpl where
  depositSc : DepositScBundle

-- ── Canonical instance ───────────────────────────────────────
-- Wires each package's Bundle fields to the corresponding `Impl/`
-- stubs. In `proof` mode, `canonical` is the curator's reference
-- implementation (given). In `codeproof` mode, `canonical` points
-- at LLM-filled defs.

def canonical : RepoImpl where
  depositSc := {
    power2                                := DepositSc.power2
    bitListToNat                          := DepositSc.bitListToNat
    natToBitList                          := DepositSc.natToBitList
    nextPath                              := DepositSc.nextPath
    zipCond                               := DepositSc.zipCond
    defaultValue                          := DepositSc.defaultValue
    zeroes                                := DepositSc.zeroes
    nodeAt                                := DepositSc.nodeAt
    siblingAt                             := DepositSc.siblingAt
    siblingValueAt                        := DepositSc.siblingValueAt
    height                                := DepositSc.height
    nodesIn                               := DepositSc.nodesIn
    leavesIn                              := DepositSc.leavesIn
    buildMerkle                           := DepositSc.buildMerkle
    computeRootLeftRightUpWithIndex       := DepositSc.computeRootLeftRightUpWithIndex
    computeLeftSiblingsOnNextpathWithIndex := DepositSc.computeLeftSiblingsOnNextpathWithIndex
    computeRootPath                        := DepositSc.computeRootPath
    computeRootLeftRightUp                 := DepositSc.computeRootLeftRightUp
    computeLeftSiblingOnNextPathFromLeftRight :=
      DepositSc.computeLeftSiblingOnNextPathFromLeftRight
    mkDeposit                             := DepositSc.mkDeposit
    deposit                               := DepositSc.deposit
    getDepositRoot                        := DepositSc.getDepositRoot
  }

-- ── joint_unsat macro ────────────────────────────────────────

/--
`joint_unsat spec_A spec_B [spec_C …] by <proof>` generates
```
theorem joint_unsat.spec_A.spec_B.… :
    ¬ ∃ impl : RepoImpl, spec_A impl ∧ spec_B impl ∧ … := by <proof>
```
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
