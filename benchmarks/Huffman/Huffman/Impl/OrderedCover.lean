import Huffman.Impl.BTree
import Huffman.Impl.Cover
import Huffman.Impl.AuxLib
import Huffman.Impl.Ordered

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Huffman.Impl.OrderedCover

Ordered-cover vocabulary translated from Coq's `OrderedCover.v`. This module
has no scored API slots; the inductive predicate below is frozen vocabulary
used by downstream specifications.
-/

inductive ordered_cover {A : Type} : List (BTree A) → BTree A → Prop where
  | intro : ∀ l t, cover l t → ordered_cover l t

namespace Huffman

end Huffman

-- !benchmark @start global_aux
-- !benchmark @end global_aux
