import Huffman.Impl.BTree
import Huffman.Impl.PBTree
import Huffman.Impl.Code

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Huffman.Impl.PBTree2BTree

Translation from partial binary trees to binary trees. The API signature is
fixed vocabulary; the function body is the curator reference implementation.

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
Implement only the function bodies.
-/

namespace Huffman

abbrev ToBtreeSig := (A : Type) → PBTree A → BTree A

end Huffman

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- !benchmark @start code_aux def=to_btree
-- !benchmark @end code_aux def=to_btree

def Huffman.to_btree : Huffman.ToBtreeSig :=
-- !benchmark @start code def=to_btree
  fun A t =>
    let rec go : PBTree A → BTree A
      | PBTree.pbleaf a => BTree.leaf a
      | PBTree.pbleft t1 => go t1
      | PBTree.pbright t1 => go t1
      | PBTree.pbnode t1 t2 => BTree.node (go t1) (go t2)
    go t
-- !benchmark @end code def=to_btree
