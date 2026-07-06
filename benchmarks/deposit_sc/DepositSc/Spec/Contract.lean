import DepositSc.Harness

/-!
# DepositSc.Spec.Contract

End-to-end correctness specs for the `Deposit` smart contract. Each
`spec_*` takes an arbitrary `impl : RepoImpl`. The `Valid` predicate
here is the Lean counterpart to Dafny's class invariant `Valid()` and
is stated *relative to `impl`* so it can be used inside other specs.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- Class invariant on a `DepositState`, relative to some `impl`.
    Mirrors the Dafny `Valid()` predicate: sizes match, counts are in
    range, ghost siblings equal the right-sibling default list, and
    `areSiblingsAtIndex` holds for the current `values`. -/
def Valid (impl : RepoImpl) (s : DepositState) : Prop :=
  1 ≤ s.treeHeight ∧
  s.branch.length = s.treeHeight ∧
  s.zeroH.length  = s.treeHeight ∧
  s.count < impl.depositSc.power2 s.treeHeight ∧
  s.values.length = s.count ∧
  s.zeroH = impl.depositSc.zeroes s.f s.default (s.treeHeight - 1) ∧
  s.zeroHashes = s.zeroH.reverse ∧
  areSiblingsAtIndex s.count
    (impl.depositSc.buildMerkle s.values s.treeHeight s.f s.default)
    s.branch s.zeroH

/-- The freshly constructed state has `count = 0`, `values = []`,
    tree height `h`, branch `l`, and preserves `f`/`d`. Dafny:
    `Deposit` constructor's `count == 0`, `TREE_HEIGHT == h`,
    `branch == l` ensures. -/
def spec_mk_deposit_fields (impl : RepoImpl) : Prop :=
  ∀ (h : Nat) (l : List Int) (f : MergeFn) (d : Int),
    let s := impl.depositSc.mkDeposit h l f d
    s.count = 0 ∧ s.values = [] ∧ s.treeHeight = h ∧
    s.f = f ∧ s.default = d ∧ s.branch = l

/-- The freshly constructed state satisfies `Valid` with an empty
    history, when the caller-supplied initial branch `l` has the
    required length `h`. Dafny: the `Deposit` constructor ensures
    `Valid()` under the analogous `|l| == h` precondition. -/
def spec_valid_initial (impl : RepoImpl) : Prop :=
  ∀ (h : Nat) (l : List Int) (f : MergeFn) (d : Int),
    1 ≤ h →
    l.length = h →
    Valid impl (impl.depositSc.mkDeposit h l f d)

/-- `deposit` preserves `Valid`, appends `v` to `values`, and
    increments `count` by 1. Dafny: `deposit`'s postconditions
    (`{:autocontracts}` implicitly asserts `Valid()` in post; the
    explicit ensures are `values == old(values) + [v]` and
    `count == old(count) + 1`). -/
def spec_deposit_preserves_valid (impl : RepoImpl) : Prop :=
  ∀ (s : DepositState) (v : Int),
    Valid impl s →
    s.count + 1 < impl.depositSc.power2 s.treeHeight →
    Valid impl (impl.depositSc.deposit s v) ∧
    (impl.depositSc.deposit s v).values = s.values ++ [v] ∧
    (impl.depositSc.deposit s v).count = s.count + 1

/-- Frame conditions on `deposit`: it does not change any constant
    field of the state (height, merge function, default, or the
    zero-hash arrays). Dafny states these implicitly via
    `{:autocontracts}` + the `const` modifier on the affected
    fields; in Lean we expose them explicitly so specs can reason
    about iterated deposits without re-proving the invariants. -/
def spec_deposit_preserves_constants (impl : RepoImpl) : Prop :=
  ∀ (s : DepositState) (v : Int),
    let s' := impl.depositSc.deposit s v
    s'.treeHeight = s.treeHeight ∧
    s'.f          = s.f ∧
    s'.default    = s.default ∧
    s'.zeroH      = s.zeroH ∧
    s'.zeroHashes = s.zeroHashes

/-- `getDepositRoot` returns the root value of `buildMerkle` over the
    deposit history. Dafny: `get_deposit_root`'s `ensures` clause. -/
def spec_deposit_root_correct (impl : RepoImpl) : Prop :=
  ∀ (s : DepositState),
    Valid impl s →
    impl.depositSc.getDepositRoot s
      = (impl.depositSc.buildMerkle s.values s.treeHeight s.f s.default).val

/-- Top-level correctness: starting from a freshly-constructed
    contract and iterating `deposit` over a value list `vs`, the
    resulting Merkle root equals the batch `buildMerkle` root over
    `vs`. This is the RunDeposit.dfy-style end-to-end claim; it
    composes `spec_valid_initial`, `spec_deposit_preserves_valid`,
    and `spec_deposit_root_correct` by induction on `vs`, and serves
    as the main correctness theorem of the deposit-sc project. -/
def spec_incremental_equals_batch (impl : RepoImpl) : Prop :=
  ∀ (h : Nat) (l : List Int) (f : MergeFn) (d : Int) (vs : List Int),
    1 ≤ h →
    l.length = h →
    vs.length < impl.depositSc.power2 h →
    impl.depositSc.getDepositRoot
        (vs.foldl impl.depositSc.deposit (impl.depositSc.mkDeposit h l f d))
      = (impl.depositSc.buildMerkle vs h f d).val
