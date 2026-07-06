import Huffman.Impl.WeightTree
import Huffman.Impl.BTree

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Huffman.Impl.SameSumLeaves

Same-sum-leaves vocabulary translated from Coq's `SameSumLeaves.v`.
This module has no scored API slots; the definition below is frozen
vocabulary used by downstream specifications.
-/

/-- `l1` and `l2` have the same multiset of leaf-sums. Mirrors upstream Coq
    `SameSumLeaves.v` (`∃ l3 l4, Permutation l1 l3 ∧ Permutation l2 l4 ∧
    map (sum_leaves f) l3 = map (sum_leaves f) l4`): the comparison is up to
    reordering, not the order-sensitive list equality a naive port would use.
    Required so `one_step_comp` holds — one-step can permute its output. -/
def same_sum_leaves {A : Type} (f : A → Nat) (l1 l2 : List (BTree A)) : Prop :=
  ∃ l3 l4 : List (BTree A),
    List.Perm l1 l3 ∧ List.Perm l2 l4 ∧
      l3.map (Huffman.sum_leaves A f) = l4.map (Huffman.sum_leaves A f)

namespace Huffman

end Huffman

-- !benchmark @start global_aux
-- !benchmark @end global_aux
