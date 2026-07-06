import SequencesV2.Impl.Trusted
import SequencesV2.Impl.Seq
import SequencesV2.Impl.MergeSort
import SequencesV2.Impl.LittleEndianNat
import SequencesV2.Impl.LittleEndianNatConversions

/-!
# SequencesV2.Bundle

Per-package implementation bundle for the `SequencesV2` translated package.
Collects all scored API signatures into one structure.

DO NOT MODIFY — benchmark infrastructure.
-/

structure SequencesV2Bundle where
  Seq_First : SequencesV2.Seq_FirstSig
  Seq_DropFirst : SequencesV2.Seq_DropFirstSig
  Seq_Last : SequencesV2.Seq_LastSig
  Seq_DropLast : SequencesV2.Seq_DropLastSig
  Seq_ToArray : SequencesV2.Seq_ToArraySig
  Seq_IndexOf : SequencesV2.Seq_IndexOfSig
  Seq_IndexOfOption : SequencesV2.Seq_IndexOfOptionSig
  Seq_LastIndexOf : SequencesV2.Seq_LastIndexOfSig
  Seq_LastIndexOfOption : SequencesV2.Seq_LastIndexOfOptionSig
  Seq_Remove : SequencesV2.Seq_RemoveSig
  Seq_RemoveValue : SequencesV2.Seq_RemoveValueSig
  Seq_Insert : SequencesV2.Seq_InsertSig
  Seq_Reverse : SequencesV2.Seq_ReverseSig
  Seq_Repeat : SequencesV2.Seq_RepeatSig
  Seq_Unzip : SequencesV2.Seq_UnzipSig
  Seq_Zip : SequencesV2.Seq_ZipSig
  Seq_Max : SequencesV2.Seq_MaxSig
  Seq_Min : SequencesV2.Seq_MinSig
  Seq_Flatten : SequencesV2.Seq_FlattenSig
  Seq_FlattenReverse : SequencesV2.Seq_FlattenReverseSig
  Seq_Map : SequencesV2.Seq_MapSig
  Seq_MapWithResult : SequencesV2.Seq_MapWithResultSig
  Seq_Filter : SequencesV2.Seq_FilterSig
  Seq_FoldLeft : SequencesV2.Seq_FoldLeftSig
  Seq_FoldRight : SequencesV2.Seq_FoldRightSig
  Seq_FlatMap : SequencesV2.Seq_FlatMapSig
  Seq_MergeSort_MergeSortBy : SequencesV2.Seq_MergeSort_MergeSortBySig
  Seq_MergeSort_MergeSortedWith : SequencesV2.Seq_MergeSort_MergeSortedWithSig
  LittleEndianNat_ToNatRight : SequencesV2.LittleEndianNat_ToNatRightSig
  LittleEndianNat_ToNatLeft : SequencesV2.LittleEndianNat_ToNatLeftSig
  LittleEndianNat_FromNat : SequencesV2.LittleEndianNat_FromNatSig
  LittleEndianNat_SeqExtend : SequencesV2.LittleEndianNat_SeqExtendSig
  LittleEndianNat_SeqExtendMultiple : SequencesV2.LittleEndianNat_SeqExtendMultipleSig
  LittleEndianNat_FromNatWithLen : SequencesV2.LittleEndianNat_FromNatWithLenSig
  LittleEndianNat_SeqZero : SequencesV2.LittleEndianNat_SeqZeroSig
  LittleEndianNat_SeqAdd : SequencesV2.LittleEndianNat_SeqAddSig
  LittleEndianNat_SeqSub : SequencesV2.LittleEndianNat_SeqSubSig
  LittleEndianNatConversions_ToSmall : SequencesV2.LittleEndianNatConversions_ToSmallSig
  LittleEndianNatConversions_ToLarge : SequencesV2.LittleEndianNatConversions_ToLargeSig
