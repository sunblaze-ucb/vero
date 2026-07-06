import DepositSc.Impl.Tree

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# DepositSc.Impl.Merkle

Merkle-tree construction and the index-based incremental-root
algorithm used by the Ethereum deposit contract. Types and spec
predicates (`isMerkle`, `areSiblingsAtIndex`) are fixed vocabulary
(DO NOT MODIFY). The three functions — `buildMerkle`,
`computeRootLeftRightUpWithIndex`, and
`computeLeftSiblingsOnNextpathWithIndex` — are `!benchmark code`
tasks.

Upstream: `src/dafny/smart/trees/MerkleTrees.dfy`,
         `src/dafny/smart/synthattribute/ComputeRootPath.dfy`,
         `src/dafny/smart/algorithms/IndexBasedAlgorithm.dfy`.
-/

namespace DepositSc

-- ── API signatures (DO NOT MODIFY) ───────────────────────────

/-!
## Sibling-array convention (used throughout this module)

Both `left` and `right` arrays — and the `areSiblingsAtIndex`
predicate — use the convention that **`left[0]` is the leaf-level
left-sibling and `left[h-1]` is the root-level left-sibling**. This is
the reverse of upstream Dafny (which stores root-level at index 0 and
leaf-level at `last`), and matches `Impl/Bits.zeroes`'s ascending
ordering so that `zeroH[0]` is the leaf-level default. The reference
implementations below and the `areSiblingsAtIndex` spec predicate
agree on this convention.
-/

/-- `buildMerkle l h f d` is the height-`h` Merkle tree whose first
    `|l|` leaves (in left-to-right order) carry the values in `l` and
    whose remaining leaves carry `d`, with every internal node
    decorated by `f`. -/
abbrev BuildMerkleSig := List Int → Nat → MergeFn → Int → Tree Int

/-- Bottom-up root computation at index `k` in a tree of height `h`,
    given the left-sibling array `left`, the right-sibling (default)
    array `right` (both length `h`, leaf-level at index 0), merge
    function `f`, and a `seed` (the value being inserted at leaf
    `k`). Dafny: `computeRootLeftRightUpWithIndex` (note the
    reversed sibling ordering — see the convention note above). -/
abbrev ComputeRootWithIndexSig :=
  Nat → Nat → List Int → List Int → MergeFn → Int → Int

/-- Bottom-up left-sibling update at index `k` in a tree of height
    `h`, yielding the `left` array that corresponds to inserting
    `seed` at leaf `k`. Length of the result equals `h`
    (leaf-level at index 0). Dafny:
    `computeLeftSiblingsOnNextpathWithIndex`. -/
abbrev ComputeLeftSiblingsWithIndexSig :=
  Nat → Nat → List Int → List Int → MergeFn → Int → List Int

/-- Path-based root computation. Given a bit path `p` (MSB-first, i.e.
    `p[0]` is the root-level step, `p.last` the leaf-level step), a
    sibling list `b` of the same length (leaf-level at index 0, root-
    level at index `|p| - 1`, ascending — matching this module's
    convention), a merge function `f`, and a `seed` value at the leaf,
    returns the recovered root value. Dafny:
    `computeRootPath<T>(p, b, f, seed)` in
    `synthattribute/GenericComputation.dfy` (converted to ascending
    sibling ordering). -/
abbrev ComputeRootPathSig :=
  Path → List Int → MergeFn → Int → Int

/-- Path-based, bottom-up root computation with split left/right
    sibling arrays. Same convention as `ComputeRootWithIndexSig`:
    `left[0]` is the leaf-level left-sibling and `left[|p| - 1]` is
    the root-level left-sibling (ascending). Dafny:
    `computeRootLeftRightUp<T>(p, left, right, f, seed)` in
    `synthattribute/ComputeRootPath.dfy`. -/
abbrev ComputeRootLeftRightUpSig :=
  Path → List Int → List Int → MergeFn → Int → Int

/-- Path-based left-sibling update. Given the current path `p`, the
    current left-sibling array `left`, the right-sibling array
    `right`, a merge function `f`, and a leaf-level seed, returns the
    updated left-sibling array along `nextPath p`. Output length
    equals `|p|`. Same ascending convention for `left` / `right` and
    the returned list. Dafny:
    `computeLeftSiblingOnNextPathFromLeftRight<T>(p, left, right, f,
    seed)` in `paths/NextPathInCompleteTreesLemmas.dfy`. -/
abbrev ComputeLeftSiblingOnNextPathFromLeftRightSig :=
  Path → List Int → List Int → MergeFn → Int → List Int

end DepositSc

-- ── Structural specs (DO NOT MODIFY) ─────────────────────────

/-- `leftLeavesMatch l t d`: the first `|l|` leaves of `t` carry the
    values in `l` (in order), and every subsequent leaf carries `d`. -/
def leftLeavesMatch (l : List Int) (t : Tree Int) (d : Int) : Prop :=
  let ls := DepositSc.leavesIn t
  ls.length ≥ l.length ∧
  (∀ i, i < l.length → (ls[i]?).map Tree.val = (l[i]?)) ∧
  (∀ i, l.length ≤ i → i < ls.length → (ls[i]?).map Tree.val = some d)

/-- `isMerkle t l f d`: `t` is complete, decorated by `f`, its left
    leaves match `l`, and its remaining leaves hold `d`. -/
def isMerkle (t : Tree Int) (l : List Int) (f : MergeFn) (d : Int) : Prop :=
  isCompleteTree t ∧ isDecoratedWith f t ∧ leftLeavesMatch l t d

/-- `areSiblingsAtIndex k t left right`: the `left` and `right` arrays
    hold, respectively, the left and right sibling values along the
    binary path to leaf `k` in `t`. Length of each must equal the
    height of `t`. -/
def areSiblingsAtIndex
    (k : Nat) (t : Tree Int) (left right : List Int) : Prop :=
  let h := t.height
  left.length = h ∧ right.length = h ∧ k < 2 ^ h ∧
    let p := DepositSc.natToBitList k h
    ∀ i, i < h →
      ((p[i]?).map Fin.val = some 1 →
        DepositSc.siblingValueAt p (i + 1) t = left[h - 1 - i]?) ∧
      ((p[i]?).map Fin.val = some 0 →
        DepositSc.siblingValueAt p (i + 1) t = right[h - 1 - i]?)

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- ── Implementations ──────────────────────────────────────────

-- !benchmark @start code_aux def=buildMerkle
-- !benchmark @end code_aux def=buildMerkle

/-- Recursive Merkle builder over `Nat` fuel (tree height). Base case:
    a leaf at height 0 carrying either `l.head?` or the default. -/
def DepositSc.buildMerkle : DepositSc.BuildMerkleSig :=
-- !benchmark @start code def=buildMerkle
  fun l h f d =>
    let rec go : Nat → List Int → Nat → Tree Int
      | 0,     xs,  idx =>
          let v := xs.headD d
          Tree.leaf v idx
      | h + 1, xs,  idx =>
          let half := 2 ^ h
          let leftXs := xs.take half
          let rightXs := xs.drop half
          let left := go h leftXs idx
          let right := go h rightXs (idx + half)
          Tree.node (f left.val right.val) left right
    go h l 0
-- !benchmark @end code def=buildMerkle

-- !benchmark @start code_aux def=computeRootLeftRightUpWithIndex
-- !benchmark @end code_aux def=computeRootLeftRightUpWithIndex

/-- At each level `i` (from `h-1` down to `0`), combine the current
    value with either `left[i]` (when `k % 2 = 1`) or `right[i]`
    (when `k % 2 = 0`), then divide `k` by 2. At level 0 the value
    is the root. -/
def DepositSc.computeRootLeftRightUpWithIndex : DepositSc.ComputeRootWithIndexSig :=
-- !benchmark @start code def=computeRootLeftRightUpWithIndex
  fun h k left right f seed =>
    let rec go : Nat → Nat → Int → Int
      | 0,     _, r => r
      | n + 1, k, r =>
          let lvl := h - 1 - n
          let bit := k % 2
          let l := (left[lvl]?).getD seed
          let rt := (right[lvl]?).getD seed
          let r' := if bit = 1 then f l r else f r rt
          go n (k / 2) r'
    go h k seed
-- !benchmark @end code def=computeRootLeftRightUpWithIndex

-- !benchmark @start code_aux def=computeLeftSiblingsOnNextpathWithIndex
-- !benchmark @end code_aux def=computeLeftSiblingsOnNextpathWithIndex

/-- Produce the left-sibling list for the path to leaf `k + 1`, given
    the left-sibling list for leaf `k`. When the path to `k + 1`
    takes a left step at some level, the new left sibling at that
    level records `seed` (or an `f`-combined value). When it takes a
    right step, the previous left sibling is preserved. -/
def DepositSc.computeLeftSiblingsOnNextpathWithIndex :
    DepositSc.ComputeLeftSiblingsWithIndexSig :=
-- !benchmark @start code def=computeLeftSiblingsOnNextpathWithIndex
  fun h k left _right f seed =>
    let rec go : Nat → Nat → Int → List Int → List Int
      | 0,     _, _,    acc => acc.reverse
      | n + 1, k, v,    acc =>
          let lvl := h - 1 - n
          let lv := (left[lvl]?).getD v
          if k % 2 = 0 then
            go n (k / 2) v (v :: acc)
          else
            go n (k / 2) (f lv v) (lv :: acc)
    go h k seed []
-- !benchmark @end code def=computeLeftSiblingsOnNextpathWithIndex

-- !benchmark @start code_aux def=computeRootPath
-- !benchmark @end code_aux def=computeRootPath

/-- Top-down walk combining a path with a generic sibling list. The
    sibling list is consumed in root-to-leaf order (ascending index in
    the tree = last in the sibling array), so we reverse once to walk
    leaf-first, mirroring `computeRootLeftRightUp`. -/
def DepositSc.computeRootPath : DepositSc.ComputeRootPathSig :=
-- !benchmark @start code def=computeRootPath
  fun p b f seed =>
    let p_rev := p.reverse
    let rec go : Path → List Int → Int → Int
      | [],       _,        acc => acc
      | bt :: bs, s :: ss,  acc =>
          let acc' := if bt.val = 0 then f acc s else f s acc
          go bs ss acc'
      | _ :: _,   [],       acc => acc
    go p_rev b seed
-- !benchmark @end code def=computeRootPath

-- !benchmark @start code_aux def=computeRootLeftRightUp
-- !benchmark @end code_aux def=computeRootLeftRightUp

/-- Bottom-up path-based root computation with separate left/right
    sibling arrays. Ascending convention: `left[0]` / `right[0]` are
    the leaf-level siblings. -/
def DepositSc.computeRootLeftRightUp : DepositSc.ComputeRootLeftRightUpSig :=
-- !benchmark @start code def=computeRootLeftRightUp
  fun p left right f seed =>
    let p_rev := p.reverse
    let rec go : Path → List Int → List Int → Int → Int
      | [],       _,       _,       acc => acc
      | bt :: bs, l :: ls, r :: rs, acc =>
          let acc' := if bt.val = 1 then f l acc else f acc r
          go bs ls rs acc'
      | _,        _,       _,       acc => acc
    go p_rev left right seed
-- !benchmark @end code def=computeRootLeftRightUp

-- !benchmark @start code_aux def=computeLeftSiblingOnNextPathFromLeftRight
-- !benchmark @end code_aux def=computeLeftSiblingOnNextPathFromLeftRight

/-- Path-based left-sibling update: when the leaf-level bit is 0 the
    new leaf-level left sibling is the seed itself, and higher levels
    carry the previous `left[i]` forward. When the leaf-level bit is
    1 the new leaf-level left sibling equals the old `left[0]` and
    the seed bubbles up through `f`. -/
def DepositSc.computeLeftSiblingOnNextPathFromLeftRight :
    DepositSc.ComputeLeftSiblingOnNextPathFromLeftRightSig :=
-- !benchmark @start code def=computeLeftSiblingOnNextPathFromLeftRight
  fun p left right f seed =>
    let p_rev := p.reverse
    let rec go : Path → List Int → List Int → Int → List Int
      | [],       _,       _,       _      => []
      | bt :: bs, l :: ls, r :: rs, running =>
          if bt.val = 0 then
            running :: go bs ls rs running
          else
            let _ := r  -- unused in this branch (mirrors Dafny)
            l :: go bs ls rs (f l running)
      | _,        _,       _,       _      => []
    go p_rev left right seed
-- !benchmark @end code def=computeLeftSiblingOnNextPathFromLeftRight
