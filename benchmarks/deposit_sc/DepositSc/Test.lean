import DepositSc.Impl.Contract

/-!
# DepositSc.Test

Executable conformance tests. `#guard` assertions exercise the
curator's reference implementations that live inside the `code`
markers in `Impl/*.lean`. Before the LLM sees the benchmark, the
pipeline replaces those marker contents with `sorry`, so these guards
also serve as regression tests on the reference itself.

Scenario taken from `src/dafny/smart/RunDeposit.dfy`:
`f = λ x y, x - y - 1`, `d = 0`, tree height `3`, deposits
`[3, 6, 2, -2, 4, 5]`.

DO NOT MODIFY — infrastructure.
-/

/-- The non-hash merge function used in the Dafny demo driver. -/
@[reducible] def demoF : MergeFn := fun x y => x - y - 1

/-- Apply a sequence of deposits to an initial state. -/
def applyDeposits (s : DepositState) : List Int → DepositState
  | []       => s
  | v :: vs  => applyDeposits (DepositSc.deposit s v) vs

/-- Initial branch for the demo scenario: all defaults, length `h = 3`. -/
@[reducible] def demoInitBranch : List Int := [0, 0, 0]

-- ── power2 ────────────────────────────────────────────────────
#guard DepositSc.power2 0 = 1
#guard DepositSc.power2 3 = 8
#guard DepositSc.power2 10 = 1024

-- ── bitListToNat / natToBitList round trip ────────────────────
#guard DepositSc.bitListToNat [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨1, by decide⟩] = 3
#guard DepositSc.bitListToNat [⟨1, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩] = 5
#guard (DepositSc.natToBitList 5 3).map Fin.val = [1, 0, 1]
#guard DepositSc.bitListToNat (DepositSc.natToBitList 5 3) = 5
#guard DepositSc.bitListToNat (DepositSc.natToBitList 0 4) = 0

-- ── nextPath is the binary successor ──────────────────────────
#guard DepositSc.bitListToNat
    (DepositSc.nextPath (DepositSc.natToBitList 3 3)) = 4
#guard DepositSc.bitListToNat
    (DepositSc.nextPath (DepositSc.natToBitList 0 3)) = 1

-- ── zipCond ───────────────────────────────────────────────────
-- c=[0,1,0] selects `a[i]` at bit=0, `b[i]` at bit=1.
#guard DepositSc.zipCond
    [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨0, by decide⟩]
    [10, 20, 30] [100, 200, 300] = [10, 200, 30]
#guard (DepositSc.zipCond [] [] []).length = 0

-- ── zeroes / defaultValue ─────────────────────────────────────
-- With f = (x,y) ↦ x - y - 1 and d = 0:
--   default 0 = 0
--   default 1 = 0 - 0 - 1 = -1
--   default 2 = -1 - (-1) - 1 = -1
#guard DepositSc.defaultValue demoF 0 0 = 0
#guard DepositSc.defaultValue demoF 0 1 = -1
#guard DepositSc.zeroes demoF 0 2 = [0, -1, -1]

-- ── buildMerkle ───────────────────────────────────────────────
-- Building over the empty list at height 1 should yield a node whose
-- two leaves carry the default, and whose value is f d d.
#guard (DepositSc.buildMerkle [] 1 demoF 0).height = 1
#guard (DepositSc.buildMerkle [] 1 demoF 0).val = demoF 0 0
-- Building at height 2 over [3] should store 3 as the leftmost leaf.
#guard match DepositSc.buildMerkle [3] 2 demoF 0 with
  | Tree.node _ (Tree.node _ (Tree.leaf v _) _) _ => v = 3
  | _ => False

-- ── Contract: initial state ───────────────────────────────────
#guard (DepositSc.mkDeposit 3 demoInitBranch demoF 0).count = 0
#guard (DepositSc.mkDeposit 3 demoInitBranch demoF 0).branch.length = 3
#guard (DepositSc.mkDeposit 3 demoInitBranch demoF 0).zeroH = DepositSc.zeroes demoF 0 2

-- ── Contract: count increments on every deposit ──────────────
#guard (applyDeposits (DepositSc.mkDeposit 3 demoInitBranch demoF 0) [3]).count = 1
#guard (applyDeposits (DepositSc.mkDeposit 3 demoInitBranch demoF 0)
          [3, 6, 2]).count = 3
#guard (applyDeposits (DepositSc.mkDeposit 3 demoInitBranch demoF 0)
          [3, 6, 2]).values = [3, 6, 2]

-- ── nodeAt / siblingAt / siblingValueAt ───────────────────────
-- Small height-1 tree: node 0 (leaf 1 idx 0) (leaf 2 idx 1).
private def testTree : Tree Int :=
  Tree.node 0 (Tree.leaf 1 0) (Tree.leaf 2 1)

#guard (DepositSc.nodeAt [] testTree).val = 0
#guard (DepositSc.nodeAt [⟨0, by decide⟩] testTree).val = 1
#guard (DepositSc.nodeAt [⟨1, by decide⟩] testTree).val = 2
#guard (DepositSc.siblingAt [⟨0, by decide⟩] testTree).val = 2
#guard (DepositSc.siblingAt [⟨1, by decide⟩] testTree).val = 1
#guard DepositSc.siblingValueAt [⟨0, by decide⟩] 1 testTree = some 2
#guard DepositSc.siblingValueAt [⟨1, by decide⟩] 1 testTree = some 1
-- Out-of-range level → none.
#guard DepositSc.siblingValueAt [⟨0, by decide⟩] 0 testTree = none
#guard DepositSc.siblingValueAt [⟨0, by decide⟩] 2 testTree = none

-- ── computeRootLeftRightUpWithIndex ───────────────────────────
-- h=1, k=0, insert seed=5 with defaults. Path is [0] (leaf bit 0):
-- r' = f seed right[0] = f 5 0 = 5 - 0 - 1 = 4.
#guard DepositSc.computeRootLeftRightUpWithIndex 1 0 [0] [0] demoF 5 = 4
-- h=1, k=1, insert seed=0 with left=[3]. Path is [1]:
-- r' = f left[0] seed = f 3 0 = 3 - 0 - 1 = 2.
#guard DepositSc.computeRootLeftRightUpWithIndex 1 1 [3] [0] demoF 0 = 2

-- ── computeLeftSiblingsOnNextpathWithIndex ────────────────────
-- h=1, k=0, seed=5: bit=0 branch pushes seed. Result: [5].
#guard DepositSc.computeLeftSiblingsOnNextpathWithIndex 1 0 [0] [0] demoF 5 = [5]
-- h=2, k=0, seed=7: two bit=0 steps push seed at both levels → [7, 7].
#guard DepositSc.computeLeftSiblingsOnNextpathWithIndex 2 0 [0, 0] [0, 0]
    demoF 7 = [7, 7]

-- ── computeRootPath (path-based, generic siblings) ────────────
-- Height 1, path = [0] (leaf bit 0), single sibling 9, seed 5:
-- combines (acc=5, sibling=9) → f 5 9 = 5 - 9 - 1 = -5.
#guard DepositSc.computeRootPath [⟨0, by decide⟩] [9] demoF 5 = -5
-- Path [1] with sibling 9, seed 5: f 9 5 = 9 - 5 - 1 = 3.
#guard DepositSc.computeRootPath [⟨1, by decide⟩] [9] demoF 5 = 3

-- ── computeRootLeftRightUp (path-based, split siblings) ───────
-- h=1, p=[0], left=[3], right=[0], seed=5: f 5 0 = 4.
#guard DepositSc.computeRootLeftRightUp [⟨0, by decide⟩] [3] [0] demoF 5 = 4
-- h=1, p=[1], left=[3], right=[0], seed=0: f 3 0 = 2.
#guard DepositSc.computeRootLeftRightUp [⟨1, by decide⟩] [3] [0] demoF 0 = 2

-- ── computeLeftSiblingOnNextPathFromLeftRight ─────────────────
-- h=1, p=[0], seed=5: output leaf-level = seed = [5].
#guard DepositSc.computeLeftSiblingOnNextPathFromLeftRight
    [⟨0, by decide⟩] [0] [0] demoF 5 = [5]
-- h=2, p=[0, 0], seed=7: both levels get pushed → [7, 7].
#guard DepositSc.computeLeftSiblingOnNextPathFromLeftRight
    [⟨0, by decide⟩, ⟨0, by decide⟩] [0, 0] [0, 0] demoF 7 = [7, 7]

-- ── getDepositRoot ────────────────────────────────────────────
-- After inserting 3 into an h=1 empty contract, root should be
-- `demoF 3 0 = 2` (matches buildMerkle [3] 1 demoF 0).val.
#guard DepositSc.getDepositRoot
    (DepositSc.deposit (DepositSc.mkDeposit 1 [0] demoF 0) 3) = 2
-- Initial root is the all-default root: `demoF 0 0 = -1`.
#guard DepositSc.getDepositRoot (DepositSc.mkDeposit 1 [0] demoF 0) = -1

-- ── height / nodesIn / leavesIn ───────────────────────────────
#guard DepositSc.height (Tree.leaf (5 : Int) 0) = 0
#guard DepositSc.height (Tree.node (1 : Int)
          (Tree.leaf 2 0) (Tree.leaf 3 1)) = 1
#guard (DepositSc.leavesIn (Tree.leaf (5 : Int) 0)).length = 1
#guard (DepositSc.leavesIn
          (Tree.node (1 : Int) (Tree.leaf 2 0) (Tree.leaf 3 1))).length = 2
#guard (DepositSc.nodesIn
          (Tree.node (1 : Int) (Tree.leaf 2 0) (Tree.leaf 3 1))).length = 3
