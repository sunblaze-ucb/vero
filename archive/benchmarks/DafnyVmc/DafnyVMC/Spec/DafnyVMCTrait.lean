import DafnyVMC.Impl.DafnyVMCTrait

/-!
# DafnyVMC.Spec.DafnyVMCTrait

Specifications for the `DafnyVMCTrait` module.  The Dafny source
(`src/DafnyVMCTrait.dfy`) marks all methods with `{:verify false}`,
indicating that formal correctness proofs are handled in separate
Dafny files (e.g. `Correctness/`).  Accordingly, this module has no
`spec_*` entries at curation time — the behavioural properties are
properties of the distribution rather than deterministic post-conditions
that can be expressed as simple equalities over `impl.<field>.<fn>`.

DO NOT MODIFY — this file is frozen curator-given content.
-/
