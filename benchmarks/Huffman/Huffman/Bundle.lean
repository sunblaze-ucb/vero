import Huffman.Impl.BTree
import Huffman.Impl.Code
import Huffman.Impl.PBTree
import Huffman.Impl.Build
import Huffman.Impl.Frequency
import Huffman.Impl.WeightTree
import Huffman.Impl.ISort
import Huffman.Impl.PBTree2BTree
import Huffman.Impl.Prod2List
import Huffman.Impl.Restrict
import Huffman.Impl.Weight
import Huffman.Impl.Huffman

/-!
# Huffman.Bundle

Per-package implementation bundle for the `Huffman` root package.
Collects the scored API signatures into one structure.

DO NOT MODIFY - benchmark infrastructure.
-/

structure HuffmanBundle where
  all_leaves            : Huffman.AllLeavesSig
  compute_code          : Huffman.ComputeCodeSig
  find_code             : Huffman.FindCodeSig
  find_val              : Huffman.FindValSig
  decode                : Huffman.DecodeSig
  encode                : Huffman.EncodeSig
  all_pbleaves          : Huffman.AllPbleavesSig
  compute_pbcode        : Huffman.ComputePbcodeSig
  pbadd                 : Huffman.PbaddSig
  pbbuild               : Huffman.PbbuildSig
  build_fun             : Huffman.BuildFunSig
  buildf                : Huffman.BuildfSig
  obuildf               : Huffman.ObuildfSig
  add_frequency_list    : Huffman.AddFrequencyListSig
  frequency_list        : Huffman.FrequencyListSig
  number_of_occurrences : Huffman.NumberOfOccurrencesSig
  sum_leaves            : Huffman.SumLeavesSig
  weight_tree           : Huffman.WeightTreeSig
  weight_tree_list      : Huffman.WeightTreeListSig
  insert                : Huffman.InsertSig
  isort                 : Huffman.IsortSig
  to_btree              : Huffman.ToBtreeSig
  prod2list             : Huffman.Prod2listSig
  restrict_code         : Huffman.RestrictCodeSig
  weight_restrict_code  : Huffman.WeightRestrictCodeSig
  weight                : Huffman.WeightSig
  huffman               : Huffman.HuffmanSig
