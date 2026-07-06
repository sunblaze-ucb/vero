import Huffman.Impl.WeightTree
import Huffman.Impl.BTree
import Huffman.Impl.Ordered
import Huffman.Impl.SameSumLeaves
import Huffman.Impl.Weight

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Huffman.Impl.OneStep

One-step Huffman tree construction vocabulary translated from Coq's
`OneStep.v`. This module has no scored API slots; the predicate below is
frozen vocabulary used by downstream specifications.
-/

def one_step {A : Type} (f : A → Nat) (l1 l2 : List (BTree A)) : Prop :=
  ∃ a b rest, ordered (sum_order f) (a :: b :: rest) ∧
    List.Perm l1 (a :: b :: rest) ∧
    List.Perm l2 (BTree.node a b :: rest)

namespace Huffman

end Huffman

-- !benchmark @start global_aux
-- !benchmark @end global_aux
