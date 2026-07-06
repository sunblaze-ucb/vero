import Huffman.Impl.BTree
import Huffman.Impl.HeightPred
import Huffman.Impl.OrderedCover
import Huffman.Impl.Cover
import Huffman.Impl.Ordered

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Huffman.Impl.SubstPred

Substitution predicate vocabulary over pairs of Huffman tree covers
translated from Coq's `SubstPred.v`. This module has no scored API slots;
the inductive predicate below is frozen vocabulary used by downstream
specifications.
-/

inductive subst_pred {A : Type} : List (BTree A) → List (BTree A) → BTree A → BTree A → Prop where
  | intro : ∀ l1 l2 t1 t2, cover l1 t1 → cover l2 t2 → subst_pred l1 l2 t1 t2

namespace Huffman

end Huffman

-- !benchmark @start global_aux
-- !benchmark @end global_aux
