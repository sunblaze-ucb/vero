import DepositSc.Harness

/-!
# DepositSc.Spec.Tree

Structural specs for the `Tree` navigation and traversal APIs.
Each `spec_*` is a property over an arbitrary `impl : RepoImpl`.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- `nodeAt []` is the identity. Dafny: `nodeAt` base case. -/
def spec_node_at_nil (impl : RepoImpl) : Prop :=
  ∀ (t : Tree Int), impl.depositSc.nodeAt [] t = t

/-- `nodeAt` on a non-leaf descends by the first bit. -/
def spec_node_at_cons (impl : RepoImpl) : Prop :=
  ∀ (b : Bit) (bs : Path) (v : Int) (l r : Tree Int),
    impl.depositSc.nodeAt (b :: bs) (Tree.node v l r)
      = impl.depositSc.nodeAt bs (if b.val = 0 then l else r)

/-- `siblingValueAt` with `i = 0` returns `none`. -/
def spec_sibling_value_at_zero (impl : RepoImpl) : Prop :=
  ∀ (p : Path) (t : Tree Int),
    impl.depositSc.siblingValueAt p 0 t = none

/-- `siblingValueAt` beyond the path length returns `none`. -/
def spec_sibling_value_at_oor (impl : RepoImpl) : Prop :=
  ∀ (p : Path) (i : Nat) (t : Tree Int),
    i > p.length →
    impl.depositSc.siblingValueAt p i t = none

/-- `height` of a leaf is 0. Dafny: `height` base case. -/
def spec_height_leaf (impl : RepoImpl) : Prop :=
  ∀ (v : Int) (idx : Nat),
    impl.depositSc.height (Tree.leaf v idx) = 0

/-- `height` of a node is `1 + max left right`. -/
def spec_height_node (impl : RepoImpl) : Prop :=
  ∀ (v : Int) (l r : Tree Int),
    impl.depositSc.height (Tree.node v l r)
      = 1 + max (impl.depositSc.height l) (impl.depositSc.height r)

/-- `leavesIn` of a leaf is a singleton list. Dafny:
    `leavesIn` base case. -/
def spec_leaves_in_leaf (impl : RepoImpl) : Prop :=
  ∀ (v : Int) (idx : Nat),
    impl.depositSc.leavesIn (Tree.leaf v idx) = [Tree.leaf v idx]

/-- `leavesIn (node _ l r) = leavesIn l ++ leavesIn r`. Dafny:
    `leavesIn` inductive case. -/
def spec_leaves_in_node (impl : RepoImpl) : Prop :=
  ∀ (v : Int) (l r : Tree Int),
    impl.depositSc.leavesIn (Tree.node v l r)
      = impl.depositSc.leavesIn l ++ impl.depositSc.leavesIn r

/-- A complete tree of height `h` has exactly `2^h` leaves. Dafny:
    `completeTreeNumberLemmas` (leaf count part). -/
def spec_height_leaves_in (impl : RepoImpl) : Prop :=
  ∀ (t : Tree Int),
    isCompleteTree t →
    (impl.depositSc.leavesIn t).length = 2 ^ impl.depositSc.height t

/-- A complete tree of height `h` has `2^(h+1) - 1` nodes. Dafny:
    `completeTreeNumberLemmas` (node count part). -/
def spec_height_nodes_in (impl : RepoImpl) : Prop :=
  ∀ (t : Tree Int),
    isCompleteTree t →
    (impl.depositSc.nodesIn t).length
      = 2 ^ (impl.depositSc.height t + 1) - 1

/-- Every element of `leavesIn` is a leaf constructor. Dafny:
    `leavesIn` postcondition. -/
def spec_leaves_in_all_leaves (impl : RepoImpl) : Prop :=
  ∀ (t : Tree Int),
    ∀ x ∈ impl.depositSc.leavesIn t, x.isLeaf = true

/-- Every leaf is also a node — `leavesIn t ⊆ nodesIn t` as multisets
    of `Tree Int`. Dafny: `leavesIn_subset_nodesIn` (used heavily in
    path proofs). -/
def spec_leaves_in_subset_nodes_in (impl : RepoImpl) : Prop :=
  ∀ (t : Tree Int),
    ∀ x ∈ impl.depositSc.leavesIn t, x ∈ impl.depositSc.nodesIn t

/-- Walking a path can only decrease height. Dafny:
    `heightOfNodeAt` in `PathInCompleteTrees.dfy`. -/
def spec_height_of_node_at_le (impl : RepoImpl) : Prop :=
  ∀ (p : Path) (t : Tree Int),
    impl.depositSc.height (impl.depositSc.nodeAt p t)
      ≤ impl.depositSc.height t

/-- Under completeness + path-fits-in-tree, the height of `nodeAt p t`
    is exactly `height t - |p|`. Dafny: `heightOfNodeAt` in
    `PathInCompleteTrees.dfy` (exact equality under its hypotheses). -/
def spec_height_of_node_at_eq (impl : RepoImpl) : Prop :=
  ∀ (p : Path) (t : Tree Int),
    isCompleteTree t →
    p.length ≤ impl.depositSc.height t →
    impl.depositSc.height (impl.depositSc.nodeAt p t)
      = impl.depositSc.height t - p.length

/-- Walking a path through a complete tree yields a complete subtree.
    Dafny: `nodeAtisCompleteAndHeight` in `PathInCompleteTrees.dfy`
    (completeness-preservation portion). -/
def spec_node_at_preserves_complete (impl : RepoImpl) : Prop :=
  ∀ (p : Path) (t : Tree Int),
    isCompleteTree t →
    p.length ≤ impl.depositSc.height t →
    isCompleteTree (impl.depositSc.nodeAt p t)

/-- `isConstant` implies every node's value equals the constant.
    Dafny: `isConstantImpliesSameValuesEveryWhere` in `Trees.dfy`. -/
def spec_is_constant_same_values (impl : RepoImpl) : Prop :=
  ∀ (t : Tree Int) (c : Int),
    isConstant c t →
    ∀ x ∈ impl.depositSc.nodesIn t, x.val = c

/-- Converse: every node's value equaling `c` implies `isConstant`.
    Dafny: `sameValuesEveryWhereImpliesIsConstant` in `Trees.dfy`. -/
def spec_same_values_is_constant (impl : RepoImpl) : Prop :=
  ∀ (t : Tree Int) (c : Int),
    (∀ x ∈ impl.depositSc.nodesIn t, x.val = c) →
    isConstant c t

/-- Complete trees of the same height have the same leaf count.
    Dafny: `completeTreesOfSameHeightHaveSameNumberOfLeaves` in
    `CompleteTrees.dfy`. -/
def spec_complete_same_height_same_leaf_count (impl : RepoImpl) : Prop :=
  ∀ (t₁ t₂ : Tree Int),
    isCompleteTree t₁ → isCompleteTree t₂ →
    impl.depositSc.height t₁ = impl.depositSc.height t₂ →
    (impl.depositSc.leavesIn t₁).length
      = (impl.depositSc.leavesIn t₂).length

/-- Both children of a complete non-leaf node have the same leaf
    count, each equal to `2^(h-1)` where `h` is the node's height.
    Dafny: `childrenInCompTreesHaveSameNumberOfLeaves`. -/
def spec_children_comp_same_leaf_count (impl : RepoImpl) : Prop :=
  ∀ (v : Int) (l r : Tree Int),
    isCompleteTree (Tree.node v l r) →
    (impl.depositSc.leavesIn l).length
      = (impl.depositSc.leavesIn r).length

/-- Both children of a complete non-leaf node have height `h - 1`
    where `h = height (node v l r)`. Dafny:
    `childrenInCompTreesHaveHeightMinusOne`. -/
def spec_children_comp_height_minus_one (impl : RepoImpl) : Prop :=
  ∀ (v : Int) (l r : Tree Int),
    isCompleteTree (Tree.node v l r) →
    impl.depositSc.height l + 1 = impl.depositSc.height (Tree.node v l r) ∧
    impl.depositSc.height r + 1 = impl.depositSc.height (Tree.node v l r)

/-- Leaf indexing distributes over children: if `node v l r` has leaves
    indexed from `i`, then `l` has leaves indexed from `i` and `r`
    from `i + 2^(height l)`. Dafny: `childrenCompTreeValidIndex`. -/
def spec_children_comp_valid_index (impl : RepoImpl) : Prop :=
  ∀ (v : Int) (l r : Tree Int) (i : Nat),
    isCompleteTree (Tree.node v l r) →
    hasLeavesIndexedFrom (Tree.node v l r) i →
    hasLeavesIndexedFrom l i ∧
    hasLeavesIndexedFrom r (i + 2 ^ impl.depositSc.height l)

/-- The leaf on the path whose bit list encodes `k` is exactly the
    `k`-th leaf of `leavesIn`. Combines `leafAtPathIsIntValueOfPath`
    and `indexOfLeafisIntValueOfPath` from `PathInCompleteTrees.dfy`. -/
def spec_leaf_at_path_is_nat_of_path (impl : RepoImpl) : Prop :=
  ∀ (p : Path) (t : Tree Int),
    isCompleteTree t →
    p.length = impl.depositSc.height t →
    impl.depositSc.bitListToNat p < (impl.depositSc.leavesIn t).length →
    (impl.depositSc.leavesIn t)[impl.depositSc.bitListToNat p]?
      = some (impl.depositSc.nodeAt p t)

/-- The first bit of a path determines which half of the leaves the
    path lands in. Dafny: `initPathDeterminesIndex` in
    `PathInCompleteTrees.dfy`. -/
def spec_init_path_determines_index (impl : RepoImpl) : Prop :=
  ∀ (b : Bit) (bs : Path) (v : Int) (l r : Tree Int),
    isCompleteTree (Tree.node v l r) →
    (bs.length + 1) = impl.depositSc.height (Tree.node v l r) →
    let k := impl.depositSc.bitListToNat (b :: bs)
    let half := 2 ^ impl.depositSc.height l
    (b.val = 0 ∧ k < half) ∨ (b.val = 1 ∧ k ≥ half)

/-- A path leading to a leaf at an index strictly less than the last
    index (so `k + 1 ≤ 2^h - 1`) must have at least one zero bit, so
    `nextPath`'s precondition holds. Dafny: `pathToLeafInInitHasZero`. -/
def spec_path_to_leaf_in_init_has_zero (impl : RepoImpl) : Prop :=
  ∀ (p : Path) (t : Tree Int),
    isCompleteTree t →
    p.length = impl.depositSc.height t →
    1 ≤ p.length →
    impl.depositSc.bitListToNat p + 1 < (impl.depositSc.leavesIn t).length →
    ∃ i, i < p.length ∧ (p[i]?).map Fin.val = some 0

/-- Walking along `nextPath p` arrives at the `(k+1)`-th leaf, where
    `k = bitListToNat p`. Dafny: `nextPathNextLeaf` in
    `NextPathInCompleteTreesLemmas.dfy`. -/
def spec_next_path_next_leaf (impl : RepoImpl) : Prop :=
  ∀ (p : Path) (t : Tree Int),
    isCompleteTree t →
    p.length = impl.depositSc.height t →
    impl.depositSc.bitListToNat p + 1 < (impl.depositSc.leavesIn t).length →
    (impl.depositSc.leavesIn t)[impl.depositSc.bitListToNat p + 1]?
      = some (impl.depositSc.nodeAt (impl.depositSc.nextPath p) t)

/-- If every leaf of an `f`-decorated complete tree has value `d`, the
    root value equals `defaultValue f d h`. Dafny:
    `allLeavesDefaultImplyRootNodeDefault` in `RightSiblings.dfy`. -/
def spec_all_leaves_default_imply_root_default (impl : RepoImpl) : Prop :=
  ∀ (t : Tree Int) (f : MergeFn) (d : Int),
    isCompleteTree t →
    isDecoratedWith f t →
    (∀ x ∈ impl.depositSc.leavesIn t, x.val = d) →
    t.val = impl.depositSc.defaultValue f d (impl.depositSc.height t)

/-- Along a path whose last `k` leaves are all default `d`, every
    right sibling equals the level's `zeroes` entry. Dafny:
    `rightSiblingsOfLastPathAreDefault` in `RightSiblings.dfy`. -/
def spec_right_siblings_of_last_path_are_default (impl : RepoImpl) : Prop :=
  ∀ (p : Path) (t : Tree Int) (f : MergeFn) (d : Int) (k idx : Nat),
    isCompleteTree t →
    isDecoratedWith f t →
    hasLeavesIndexedFrom t idx →
    p.length = impl.depositSc.height t →
    impl.depositSc.bitListToNat p = k →
    (∀ x ∈ impl.depositSc.leavesIn t,
      ∀ j, idx + k < j → x.val = d) →
    ∀ i, i < p.length → (p[i]?).map Fin.val = some 0 →
      impl.depositSc.siblingValueAt p (i + 1) t
        = (impl.depositSc.zeroes f d (impl.depositSc.height t - 1))[impl.depositSc.height t - 1 - i]?

/-- Two trees agreeing on all leaves (except possibly at a single
    index) share every sibling along the path to any shared-leaf
    index. Dafny: `siblingsInEquivTreesAreEqual` in `Siblings.dfy`. -/
def spec_siblings_in_equiv_trees_are_equal (impl : RepoImpl) : Prop :=
  ∀ (p : Path) (t t' : Tree Int) (f : MergeFn) (k idx : Nat),
    isCompleteTree t → isCompleteTree t' →
    isDecoratedWith f t → isDecoratedWith f t' →
    impl.depositSc.height t = impl.depositSc.height t' →
    p.length = impl.depositSc.height t →
    impl.depositSc.bitListToNat p = k →
    hasLeavesIndexedFrom t idx →
    hasLeavesIndexedFrom t' idx →
    (∀ j, j ≠ k → j < (impl.depositSc.leavesIn t).length →
      (impl.depositSc.leavesIn t)[j]?.map Tree.val
        = (impl.depositSc.leavesIn t')[j]?.map Tree.val) →
    ∀ i, i < p.length →
      impl.depositSc.siblingValueAt p (i + 1) t
        = impl.depositSc.siblingValueAt p (i + 1) t'

/-- Two `f`-decorated complete trees with identical leaf values have
    the same root value. Dafny: `sameLeavesSameRoot` in
    `SiblingsPlus.dfy`. -/
def spec_same_leaves_same_root (impl : RepoImpl) : Prop :=
  ∀ (t t' : Tree Int) (f : MergeFn),
    isCompleteTree t → isCompleteTree t' →
    isDecoratedWith f t → isDecoratedWith f t' →
    impl.depositSc.height t = impl.depositSc.height t' →
    (∀ i, i < (impl.depositSc.leavesIn t).length →
      (impl.depositSc.leavesIn t)[i]?.map Tree.val
        = (impl.depositSc.leavesIn t')[i]?.map Tree.val) →
    t.val = t'.val
