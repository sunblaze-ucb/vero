import DepositSc.Impl.Bits

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# DepositSc.Impl.Tree

Binary tree datatype and path-navigation primitives. A `Tree Int`
decorated with a merge function `f : MergeFn` captures a Merkle tree
of fixed height.

Types, signatures, and the three predicates (`isCompleteTree`,
`isDecoratedWith`, `hasLeavesIndexedFrom`) are fixed vocabulary (DO
NOT MODIFY). The three navigation functions (`nodeAt`, `siblingAt`,
`siblingValueAt`) are `!benchmark code` tasks.

Upstream: `src/dafny/smart/trees/{Trees.dfy,CompleteTrees.dfy}`,
         `src/dafny/smart/paths/PathInCompleteTrees.dfy`.
-/

-- ── Core data types (DO NOT MODIFY) ──────────────────────────

/-- A binary tree with values of type `α` at every node.

    `leaf v idx` — a leaf carrying value `v`, indexed by `idx` (the
    position of the leaf in left-to-right order; Dafny's ghost field
    is promoted to a real Nat here since Lean has no ghost state).

    `node v left right` — an internal node with value `v` and two
    subtrees. -/
inductive Tree (α : Type) where
  | leaf (v : α) (idx : Nat) : Tree α
  | node (v : α) (left right : Tree α) : Tree α
  deriving Inhabited

namespace Tree

/-- Value at the root (fully defined vocabulary; curator-given). -/
def val {α : Type} : Tree α → α
  | leaf v _     => v
  | node v _ _   => v

/-- Is this tree a leaf constructor? -/
def isLeaf {α : Type} : Tree α → Bool
  | leaf _ _   => true
  | node _ _ _ => false

/-- Curator-given height. Exposed via `impl.height` (the benchmark
    API) but kept as a `Tree` method for use inside frozen specs /
    predicates where we must not reference `impl`. -/
def height {α : Type} : Tree α → Nat
  | leaf _ _        => 0
  | node _ l r      => 1 + max (height l) (height r)

end Tree

namespace DepositSc

-- ── API signatures (DO NOT MODIFY) ───────────────────────────

/-- Follow a path through a complete tree, bit 0 = go left,
    bit 1 = go right. Stops early if the path is empty or overruns. -/
abbrev NodeAtSig         := Path → Tree Int → Tree Int

/-- The sibling of the node at the end of the path (flip the last
    bit). -/
abbrev SiblingAtSig      := Path → Tree Int → Tree Int

/-- Value of the sibling along path `p` at level `i` (`i` in `1..|p|`).
    Returns `none` for out-of-range `i`. -/
abbrev SiblingValueAtSig := Path → Nat → Tree Int → Option Int

/-- Tree height. A leaf has height 0; a node has height
    `1 + max (height left) (height right)`. -/
abbrev HeightSig    := Tree Int → Nat

/-- Nodes in pre-order traversal. -/
abbrev NodesInSig   := Tree Int → List (Tree Int)

/-- Leaves left-to-right. -/
abbrev LeavesInSig  := Tree Int → List (Tree Int)

end DepositSc

-- ── Structural predicates (DO NOT MODIFY) ────────────────────

/-- Every internal node's value equals `f (left.val) (right.val)`. -/
def isDecoratedWith (f : MergeFn) : Tree Int → Prop
  | Tree.leaf _ _      => True
  | Tree.node v l r    => v = f l.val r.val ∧ isDecoratedWith f l ∧ isDecoratedWith f r

/-- The tree has equal-height subtrees at every internal node.
    Uses `Tree.height` (curator-given) so it's usable inside frozen
    specs without referencing `impl`. -/
def isCompleteTree {α : Type} : Tree α → Prop
  | Tree.leaf _ _      => True
  | Tree.node _ l r    => l.height = r.height
                          ∧ isCompleteTree l ∧ isCompleteTree r

/-- All leaves, read left-to-right, are indexed consecutively starting
    from `i` (so leaves inside the full tree are numbered
    `i, i+1, …`). -/
def hasLeavesIndexedFrom {α : Type} : Tree α → Nat → Prop
  | Tree.leaf _ k,   i => k = i
  | Tree.node _ l r, i =>
      ∃ m, hasLeavesIndexedFrom l i ∧ hasLeavesIndexedFrom r (i + m)
      ∧ m = 2 ^ l.height

/-- Every node (leaves and internals) in the tree carries value `c`.
    Dafny: `predicate isConstant<T>(r : Tree<T>, c: T)` in `Trees.dfy`. -/
def isConstant {α : Type} (c : α) : Tree α → Prop
  | Tree.leaf v _      => v = c
  | Tree.node v l r    => v = c ∧ isConstant c l ∧ isConstant c r

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- ── Implementations ──────────────────────────────────────────

-- !benchmark @start code_aux def=nodeAt
-- !benchmark @end code_aux def=nodeAt

def DepositSc.nodeAt : DepositSc.NodeAtSig :=
-- !benchmark @start code def=nodeAt
  fun path t =>
    match path, t with
    | [],        t                => t
    | b :: bs,   Tree.node _ l r  =>
        DepositSc.nodeAt bs (if b.val = 0 then l else r)
    | _ :: _,    t                => t
-- !benchmark @end code def=nodeAt

-- !benchmark @start code_aux def=siblingAt
-- !benchmark @end code_aux def=siblingAt

def DepositSc.siblingAt : DepositSc.SiblingAtSig :=
-- !benchmark @start code def=siblingAt
  fun path t =>
    match path with
    | []          => t
    | _           =>
      let last := path.getLastD ⟨0, by decide⟩
      let flipped : Bit := ⟨1 - last.val, by
        have := last.isLt; omega⟩
      let rerouted := path.dropLast ++ [flipped]
      DepositSc.nodeAt rerouted t
-- !benchmark @end code def=siblingAt

-- !benchmark @start code_aux def=siblingValueAt
-- !benchmark @end code_aux def=siblingValueAt

def DepositSc.siblingValueAt : DepositSc.SiblingValueAtSig :=
-- !benchmark @start code def=siblingValueAt
  fun path i t =>
    if i = 0 ∨ i > path.length then none
    else some (DepositSc.siblingAt (path.take i) t).val
-- !benchmark @end code def=siblingValueAt

-- !benchmark @start code_aux def=height
-- !benchmark @end code_aux def=height

def DepositSc.height : DepositSc.HeightSig :=
-- !benchmark @start code def=height
  fun t => t.height
-- !benchmark @end code def=height

-- !benchmark @start code_aux def=nodesIn
-- !benchmark @end code_aux def=nodesIn

def DepositSc.nodesIn : DepositSc.NodesInSig :=
-- !benchmark @start code def=nodesIn
  fun t =>
    match t with
    | Tree.leaf _ _       => [t]
    | Tree.node _ l r     => t :: (DepositSc.nodesIn l ++ DepositSc.nodesIn r)
-- !benchmark @end code def=nodesIn

-- !benchmark @start code_aux def=leavesIn
-- !benchmark @end code_aux def=leavesIn

def DepositSc.leavesIn : DepositSc.LeavesInSig :=
-- !benchmark @start code def=leavesIn
  fun t =>
    match t with
    | Tree.leaf _ _       => [t]
    | Tree.node _ l r     => DepositSc.leavesIn l ++ DepositSc.leavesIn r
-- !benchmark @end code def=leavesIn
