import DepositSc.Harness

/-!
# DepositSc.Spec.Merkle

Specifications for the Merkle construction and the index-based
incremental algorithm. Each `spec_*` takes an arbitrary
`impl : RepoImpl`.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- `buildMerkle l h f d` produces a tree of height exactly `h`. -/
def spec_build_merkle_height (impl : RepoImpl) : Prop :=
  ∀ (l : List Int) (h : Nat) (f : MergeFn) (d : Int),
    l.length ≤ impl.depositSc.power2 h →
    impl.depositSc.height (impl.depositSc.buildMerkle l h f d) = h

/-- `buildMerkle l h f d` is complete. Dafny: `buildMerkle` post. -/
def spec_build_merkle_is_complete (impl : RepoImpl) : Prop :=
  ∀ (l : List Int) (h : Nat) (f : MergeFn) (d : Int),
    l.length ≤ impl.depositSc.power2 h →
    isCompleteTree (impl.depositSc.buildMerkle l h f d)

/-- Each internal node of `buildMerkle l h f d` is `f`-decorated. -/
def spec_build_merkle_is_decorated (impl : RepoImpl) : Prop :=
  ∀ (l : List Int) (h : Nat) (f : MergeFn) (d : Int),
    l.length ≤ impl.depositSc.power2 h →
    isDecoratedWith f (impl.depositSc.buildMerkle l h f d)

/-- `buildMerkle l h f d` is an `isMerkle`-tree for `(l, f, d)`.
    Dafny: `buildMerkle` has this as an `ensures` clause. -/
def spec_build_merkle_is_merkle (impl : RepoImpl) : Prop :=
  ∀ (l : List Int) (h : Nat) (f : MergeFn) (d : Int),
    l.length ≤ impl.depositSc.power2 h →
    isMerkle (impl.depositSc.buildMerkle l h f d) l f d

/-- The first `|l|` leaves of `buildMerkle l h f d` carry the values
    in `l`, in order. Dafny: `buildMerkle` post (leftLeavesMatch). -/
def spec_build_merkle_leaves (impl : RepoImpl) : Prop :=
  ∀ (l : List Int) (h : Nat) (f : MergeFn) (d : Int) (i : Nat),
    l.length ≤ impl.depositSc.power2 h →
    i < l.length →
    ((impl.depositSc.leavesIn (impl.depositSc.buildMerkle l h f d))[i]?).map Tree.val = l[i]?

/-- Leaves beyond `|l|` in `buildMerkle l h f d` carry the default
    `d`. Dafny: `buildMerkle` post (leftLeavesMatch, right half). -/
def spec_build_merkle_leaves_default (impl : RepoImpl) : Prop :=
  ∀ (l : List Int) (h : Nat) (f : MergeFn) (d : Int) (i : Nat),
    l.length ≤ impl.depositSc.power2 h →
    l.length ≤ i →
    i < (impl.depositSc.leavesIn (impl.depositSc.buildMerkle l h f d)).length →
    ((impl.depositSc.leavesIn (impl.depositSc.buildMerkle l h f d))[i]?).map Tree.val = some d

/-- `buildMerkle` assigns consecutive leaf indices starting at 0.
    Dafny: `buildMerkle` post (hasLeavesIndexedFrom). -/
def spec_build_merkle_indices (impl : RepoImpl) : Prop :=
  ∀ (l : List Int) (h : Nat) (f : MergeFn) (d : Int),
    l.length ≤ impl.depositSc.power2 h →
    hasLeavesIndexedFrom (impl.depositSc.buildMerkle l h f d) 0

/-- `nodeAt [] t = t`: the empty path lands at the root. -/
def spec_node_at_root (impl : RepoImpl) : Prop :=
  ∀ (t : Tree Int), impl.depositSc.nodeAt [] t = t

/-- `nodeAt` result height. On a complete tree, following a length-`k`
    path descends exactly `k` levels. Dafny: `nodeAt_height`. -/
def spec_node_at_height (impl : RepoImpl) : Prop :=
  ∀ (t : Tree Int) (p : Path),
    isCompleteTree t →
    p.length ≤ impl.depositSc.height t →
    impl.depositSc.height (impl.depositSc.nodeAt p t)
      = impl.depositSc.height t - p.length

/-- `nodeAt` is always a member of `nodesIn` on complete trees.
    Dafny: `nodeAt_mem_nodesIn`. -/
def spec_node_at_mem_nodes_in (impl : RepoImpl) : Prop :=
  ∀ (t : Tree Int) (p : Path),
    isCompleteTree t →
    p.length ≤ impl.depositSc.height t →
    impl.depositSc.nodeAt p t ∈ impl.depositSc.nodesIn t

/-- The index-based root computation recovers `buildMerkle`'s root
    value, given a correct sibling arrangement. Dafny:
    `computeRootIsCorrect`. -/
def spec_compute_root_correct (impl : RepoImpl) : Prop :=
  ∀ (l : List Int) (h : Nat) (f : MergeFn) (d : Int)
    (left : List Int),
    l.length < impl.depositSc.power2 h →
    areSiblingsAtIndex l.length (impl.depositSc.buildMerkle l h f d)
        left (impl.depositSc.zeroes f d (h - 1)) →
    impl.depositSc.computeRootLeftRightUpWithIndex
        h l.length left (impl.depositSc.zeroes f d (h - 1)) f d
      = (impl.depositSc.buildMerkle l h f d).val

/-- The index-based left-sibling update preserves the
    `areSiblingsAtIndex` invariant. Dafny: `computeNewLeftIsCorrect`. -/
def spec_compute_left_sibling_correct (impl : RepoImpl) : Prop :=
  ∀ (l : List Int) (a : Int) (h : Nat) (f : MergeFn) (d : Int)
    (left : List Int),
    l.length + 1 < impl.depositSc.power2 h →
    areSiblingsAtIndex l.length (impl.depositSc.buildMerkle l h f d)
        left (impl.depositSc.zeroes f d (h - 1)) →
    let newLeft :=
      impl.depositSc.computeLeftSiblingsOnNextpathWithIndex
        h l.length left (impl.depositSc.zeroes f d (h - 1)) f a
    areSiblingsAtIndex (l.length + 1)
      (impl.depositSc.buildMerkle (l ++ [a]) h f d)
      newLeft (impl.depositSc.zeroes f d (h - 1))

/-- `computeLeftSiblingsOnNextpathWithIndex` output has length equal
    to `h` (matches the `left`/`right` input lengths). -/
def spec_compute_left_siblings_length (impl : RepoImpl) : Prop :=
  ∀ (h k : Nat) (left right : List Int) (f : MergeFn) (seed : Int),
    left.length = h → right.length = h → k < impl.depositSc.power2 h →
    (impl.depositSc.computeLeftSiblingsOnNextpathWithIndex
        h k left right f seed).length = h

/-- The generic path-based root computation yields the tree's root
    value when the sibling array matches the tree's siblings along
    the path. Dafny: `computeOnPathYieldsRootValue` in
    `synthattribute/GenericComputation.dfy`. -/
def spec_compute_root_path_correct (impl : RepoImpl) : Prop :=
  ∀ (p : Path) (t : Tree Int) (b : List Int) (f : MergeFn) (seed : Int),
    isCompleteTree t →
    isDecoratedWith f t →
    p.length = impl.depositSc.height t →
    b.length = p.length →
    (impl.depositSc.nodeAt p t).val = seed →
    (∀ i, i < p.length →
      impl.depositSc.siblingValueAt p (i + 1) t = b[p.length - 1 - i]?) →
    impl.depositSc.computeRootPath p b f seed = t.val

/-- The bottom-up path-based root computation agrees with the tree's
    root value when the left/right sibling arrays are correct for
    the path. Dafny: `computeRootLeftRightUpIsCorrectForTree` in
    `synthattribute/ComputeRootPath.dfy`. -/
def spec_compute_root_up_correct (impl : RepoImpl) : Prop :=
  ∀ (p : Path) (t : Tree Int) (left right : List Int) (f : MergeFn) (seed : Int),
    isCompleteTree t →
    isDecoratedWith f t →
    p.length = impl.depositSc.height t →
    left.length = p.length →
    right.length = p.length →
    (impl.depositSc.nodeAt p t).val = seed →
    (∀ i, i < p.length →
      ((p[i]?).map Fin.val = some 1 →
        impl.depositSc.siblingValueAt p (i + 1) t = left[p.length - 1 - i]?) ∧
      ((p[i]?).map Fin.val = some 0 →
        impl.depositSc.siblingValueAt p (i + 1) t = right[p.length - 1 - i]?)) →
    impl.depositSc.computeRootLeftRightUp p left right f seed = t.val

/-- The path-based left-sibling update produces a new left array that
    is correct for `nextPath p`, relative to the same tree. Dafny:
    `computeLeftSiblingOnNextPathFromLeftRightIsCorrectInATree` in
    `paths/NextPathInCompleteTreesLemmas.dfy`. -/
def spec_compute_new_left_path_correct (impl : RepoImpl) : Prop :=
  ∀ (p : Path) (t : Tree Int) (left right : List Int) (f : MergeFn) (seed : Int),
    isCompleteTree t →
    isDecoratedWith f t →
    p.length = impl.depositSc.height t →
    left.length = p.length →
    right.length = p.length →
    (impl.depositSc.nodeAt p t).val = seed →
    (∃ i, i < p.length ∧ (p[i]?).map Fin.val = some 0) →
    (∀ i, i < p.length →
      ((p[i]?).map Fin.val = some 1 →
        impl.depositSc.siblingValueAt p (i + 1) t = left[p.length - 1 - i]?) ∧
      ((p[i]?).map Fin.val = some 0 →
        impl.depositSc.siblingValueAt p (i + 1) t = right[p.length - 1 - i]?)) →
    let np := impl.depositSc.nextPath p
    let newLeft :=
      impl.depositSc.computeLeftSiblingOnNextPathFromLeftRight p left right f seed
    ∀ i, i < np.length →
      ((np[i]?).map Fin.val = some 1 →
        impl.depositSc.siblingValueAt np (i + 1) t = newLeft[np.length - 1 - i]?)

/-- Right siblings along the path to the last filled leaf position
    are all default values. Dafny: `rightOfPathToLastIsZero` in
    `MerkleTrees.dfy`. -/
def spec_right_of_path_to_last_is_zero (impl : RepoImpl) : Prop :=
  ∀ (l : List Int) (h : Nat) (f : MergeFn) (d : Int),
    1 ≤ h → l.length < impl.depositSc.power2 h →
    let t := impl.depositSc.buildMerkle l h f d
    let p := impl.depositSc.natToBitList l.length h
    ∀ i, i < h → (p[i]?).map Fin.val = some 0 →
      impl.depositSc.siblingValueAt p (i + 1) t
        = (impl.depositSc.zeroes f d (h - 1))[h - 1 - i]?

/-- `buildMerkle l h f d` and `buildMerkle (l ++ [a]) h f d` share
    every leaf except the one at position `|l|`. Dafny:
    `equivTreesSameLeaves` in `MerkleTrees.dfy`. -/
def spec_equiv_trees_same_leaves (impl : RepoImpl) : Prop :=
  ∀ (l : List Int) (a : Int) (h : Nat) (f : MergeFn) (d : Int),
    l.length + 1 ≤ impl.depositSc.power2 h →
    let t  := impl.depositSc.buildMerkle l h f d
    let t' := impl.depositSc.buildMerkle (l ++ [a]) h f d
    ∀ i, i ≠ l.length → i < (impl.depositSc.leavesIn t).length →
      (impl.depositSc.leavesIn t)[i]?.map Tree.val
        = (impl.depositSc.leavesIn t')[i]?.map Tree.val

/-- Core commutativity: running `computeRootLeftRightUp` with the
    old left-sibling array yields the same root as running it with
    the freshly-updated left-sibling array. This is the lemma that
    powers the "incremental equals batch" correctness chain. Dafny:
    `computeRootAndUpdateLeftSiblingsCommutes` in
    `algorithms/CommuteProof.dfy`. -/
def spec_compute_root_commutes (impl : RepoImpl) : Prop :=
  ∀ (p : Path) (left right : List Int) (f : MergeFn) (seed : Int),
    left.length = p.length →
    right.length = p.length →
    impl.depositSc.computeRootLeftRightUp p left right f seed
      = impl.depositSc.computeRootLeftRightUp p
          (impl.depositSc.computeLeftSiblingOnNextPathFromLeftRight
              p left right f seed)
          right f seed

/-- Alternative form of incremental-equals-batch: running
    `computeRootLeftRightUp` on `p` equals running it on `nextPath p`
    with the updated left siblings and a default seed. Dafny:
    `computeRootUsingNextPath` in `algorithms/CommuteProof.dfy`. -/
def spec_compute_root_using_next_path (impl : RepoImpl) : Prop :=
  ∀ (p : Path) (left right : List Int) (f : MergeFn) (seed d : Int),
    left.length = p.length →
    right.length = p.length →
    right = impl.depositSc.zeroes f d (p.length - 1) →
    (∃ i, i < p.length ∧ (p[i]?).map Fin.val = some 0) →
    impl.depositSc.computeRootLeftRightUp p left right f seed
      = impl.depositSc.computeRootLeftRightUp
          (impl.depositSc.nextPath p)
          (impl.depositSc.computeLeftSiblingOnNextPathFromLeftRight
              p left right f seed)
          right f d
