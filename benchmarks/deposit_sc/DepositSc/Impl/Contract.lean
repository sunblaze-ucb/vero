import DepositSc.Impl.Merkle

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# DepositSc.Impl.Contract

The `Deposit` smart contract state and methods. `DepositState`
mirrors the Dafny class, materialising the Dafny ghost fields that
the spec actually needs: `zero_h` → `zeroH` and `values` → `values`.
Dafny's other ghost `rBranch` is deliberately omitted — it equals
`reverse(branch)` by invariant, and since Lean carries everything
pure-functionally we can derive it on demand via `.reverse` wherever
a spec wants it. The three methods — `mkDeposit` (constructor),
`deposit`, and `getDepositRoot` — are `!benchmark code` tasks.

Upstream: `src/dafny/smart/DepositSmart.dfy`.
-/

-- ── Core data type (DO NOT MODIFY) ───────────────────────────

/-- State of the incremental Merkle-tree smart contract.

    Dafny's class has a mix of `const` fields (`d`, `f`,
    `TREE_HEIGHT`, `zero_hashes`, ghost `zero_h`) and mutable fields
    (`branch`, `count`, ghost `rBranch`, ghost `values`). We flatten
    the spec-relevant ones into one record. `rBranch` (Dafny's
    reverse-view of `branch`) is NOT stored — downstream specs that
    want it write `s.branch.reverse`. `values` carries the deposit
    history the Dafny spec expresses with `ghost var`. -/
structure DepositState where
  /-- Tree height `h ≥ 1`. -/
  treeHeight : Nat
  /-- Merge function (originally a hash). -/
  f          : MergeFn
  /-- Default leaf value. -/
  default    : Int
  /-- Left-sibling values on the path to leaf `count`. Length `= h`. -/
  branch     : List Int
  /-- Precomputed zero-hashes. Length `= h`. -/
  zeroHashes : List Int
  /-- Ghost: right-sibling (default-hash) values on the path to leaf
      `count`, stored MSB-first (length `= h`). -/
  zeroH      : List Int
  /-- Number of deposits made so far. -/
  count      : Nat
  /-- Ghost: the deposit history so far. -/
  values     : List Int
  deriving Inhabited

namespace DepositSc

-- ── API signatures (DO NOT MODIFY) ───────────────────────────

/-- Constructor. `mkDeposit h l f d` initialises a contract with
    tree height `h`, initial branch (left-sibling list on the path to
    leaf 0) `l`, merge function `f`, and default leaf value `d`.
    Precondition: `l.length = h`. Dafny:
    `Deposit.init(h, l, f, default)` at `DepositSmart.dfy:123`. -/
abbrev MkDepositSig       := Nat → List Int → MergeFn → Int → DepositState

/-- Deposit value `v`, returning the updated state. -/
abbrev DepositSig         := DepositState → Int → DepositState

/-- Compute the current Merkle root. -/
abbrev GetDepositRootSig  := DepositState → Int

end DepositSc

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- ── Implementations ──────────────────────────────────────────

-- !benchmark @start code_aux def=mkDeposit
-- !benchmark @end code_aux def=mkDeposit

def DepositSc.mkDeposit : DepositSc.MkDepositSig :=
-- !benchmark @start code def=mkDeposit
  fun h l f d =>
    let zh := DepositSc.zeroes f d (h - 1)
    { treeHeight := h
    , f          := f
    , default    := d
    , branch     := l
    , zeroHashes := zh.reverse
    , zeroH      := zh
    , count      := 0
    , values     := [] }
-- !benchmark @end code def=mkDeposit

-- !benchmark @start code_aux def=deposit
-- !benchmark @end code_aux def=deposit

/-- Walk up the tree so long as the lowest bit is 1, folding `f` over
    the current branch, then store the running value as the new left
    sibling. Increment `count` and append `v` to `values`. -/
def DepositSc.deposit : DepositSc.DepositSig :=
-- !benchmark @start code def=deposit
  fun s v =>
    let h := s.treeHeight
    let newBranch :=
      DepositSc.computeLeftSiblingsOnNextpathWithIndex
        h s.count s.branch s.zeroH s.f v
    { s with
        branch := newBranch
      , count  := s.count + 1
      , values := s.values ++ [v] }
-- !benchmark @end code def=deposit

-- !benchmark @start code_aux def=getDepositRoot
-- !benchmark @end code_aux def=getDepositRoot

def DepositSc.getDepositRoot : DepositSc.GetDepositRootSig :=
-- !benchmark @start code def=getDepositRoot
  fun s =>
    DepositSc.computeRootLeftRightUpWithIndex
      s.treeHeight s.count s.branch s.zeroH s.f s.default
-- !benchmark @end code def=getDepositRoot
