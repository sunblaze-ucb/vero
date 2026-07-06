import Huffman.Impl.BTree
import Huffman.Impl.Code
import Huffman.Impl.PBTree
import Huffman.Impl.AuxLib
import Huffman.Impl.Build
import Huffman.Impl.Cover
import Huffman.Impl.CoverMin
import Huffman.Impl.Frequency
import Huffman.Impl.HeightPred
import Huffman.Impl.OneStep
import Huffman.Impl.Ordered
import Huffman.Impl.OrderedCover
import Huffman.Impl.SameSumLeaves
import Huffman.Impl.SubstPred
import Huffman.Impl.UniqueKey
import Huffman.Impl.WeightTree
import Huffman.Impl.ISort
import Huffman.Impl.PBTree2BTree
import Huffman.Impl.Prod2List
import Huffman.Impl.Restrict
import Huffman.Impl.Weight
import Huffman.Impl.Huffman

/-!
# Huffman.Test

Executable conformance tests for curator reference implementations.

DO NOT MODIFY - infrastructure.
-/

#guard Huffman.all_leaves Nat (BTree.leaf 3) == [3]
#guard number_of_nodes (BTree.leaf 3) == 0
#guard id_list 7 3 == [7, 7, 7]
#guard Huffman.find_code Nat 0 ([] : Code Nat) == []
#guard Huffman.frequency_list Nat ([] : List Nat) == []
