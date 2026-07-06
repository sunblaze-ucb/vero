import Huffman.Impl.WeightTree
import Huffman.Impl.BTree
import Huffman.Impl.Cover
import Huffman.Impl.AuxLib

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Huffman.Impl.CoverMin

Minimum-cover vocabulary translated from Coq's `CoverMin.v`. This module has
no scored API slots; the definition below is frozen vocabulary used by
downstream specifications.
-/

def cover_min (A : Type) (f : A → Nat) (l : List (BTree A)) (t1 : BTree A) : Prop :=
  cover l t1 ∧ ∀ t2, cover l t2 → Huffman.weight_tree A f t1 ≤ Huffman.weight_tree A f t2

namespace Huffman

end Huffman

-- !benchmark @start global_aux
-- !benchmark @end global_aux
