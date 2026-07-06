import Bidict.Bundle

/-!
# Bidict.Harness

Benchmark harness: `RepoImpl` structure (one field for the `Bidict` package),
`canonical` instance wiring all 31 reference implementations, and the
`joint_unsat` macro for joint unsatisfiability proofs.

DO NOT MODIFY — benchmark infrastructure.
-/

structure RepoImpl where
  bidict : BidictBundle

def canonical : RepoImpl where
  bidict := {
    -- BidictBase (8)
    inverse              := @Bidict.inverse
    inv                  := @Bidict.inv
    copy                 := @Bidict.copy
    union                := @Bidict.union
    runion               := @Bidict.runion
    length               := @Bidict.length
    iter                 := @Bidict.iter
    getitem              := @Bidict.getitem
    -- Iter (2)
    iteritems            := @Bidict.iteritems
    inverted             := @Bidict.inverted
    -- FrozenBidict (1)
    frozenBidictHash     := @Bidict.frozenBidictHash
    -- MutableBidict (10)
    initMutableBidict    := @Bidict.initMutableBidict
    delItem              := @Bidict.delItem
    setItem              := @Bidict.setItem
    forceput             := @Bidict.forceput
    clear                := @Bidict.clear
    pop                  := @Bidict.pop
    popitem              := @Bidict.popitem
    update               := @Bidict.update
    forceupdate          := @Bidict.forceupdate
    putall               := @Bidict.putall
    -- OrderedBidict (10)
    initOrderedBidict    := @Bidict.initOrderedBidict
    iterOrderedBidict    := @Bidict.iterOrderedBidict
    inverseOrderedBidict := @Bidict.inverseOrderedBidict
    invOrderedBidict     := @Bidict.invOrderedBidict
    clearOrderedBidict   := @Bidict.clearOrderedBidict
    popOrderedBidict     := @Bidict.popOrderedBidict
    popitemOrderedBidict := @Bidict.popitemOrderedBidict
    moveToEndOrderedBidict := @Bidict.moveToEndOrderedBidict
    keysOrderedBidict    := @Bidict.keysOrderedBidict
    itemsOrderedBidict   := @Bidict.itemsOrderedBidict
  }

/-- `joint_unsat spec_A spec_B [spec_C …] by <proof>` generates the
    ∧-conjunction unsat theorem. Variadic; no sort / no dedup — anti-cheat
    is enforced at `!solution` extraction during evaluation. -/
syntax "joint_unsat" ident ident ident* "by" tacticSeq : command

open Lean in
macro_rules
  | `(joint_unsat $s1 $s2 $[$rest]* by $proof) => do
    let specs := #[s1, s2] ++ rest
    let name := specs.foldl (init := `joint_unsat) fun acc s =>
      Name.append acc s.getId
    let mut body ← `($(specs[0]!) impl)
    for s in specs[1:] do
      body ← `($body ∧ $s impl)
    `(theorem $(mkIdent name) : ¬ ∃ impl : RepoImpl, $body := by $proof)
