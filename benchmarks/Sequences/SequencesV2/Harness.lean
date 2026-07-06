import SequencesV2.Bundle

/-!
# SequencesV2.Harness

Benchmark harness: `RepoImpl` structure, canonical implementation wiring,
and the `joint_unsat` macro consumed by downstream codeproof artifacts.

DO NOT MODIFY — benchmark infrastructure.
-/

structure RepoImpl where
  sequences : SequencesV2Bundle

def canonical : RepoImpl where
  sequences := {
    Seq_First := SequencesV2.Seq_First
    Seq_DropFirst := SequencesV2.Seq_DropFirst
    Seq_Last := SequencesV2.Seq_Last
    Seq_DropLast := SequencesV2.Seq_DropLast
    Seq_ToArray := SequencesV2.Seq_ToArray
    Seq_IndexOf := SequencesV2.Seq_IndexOf
    Seq_IndexOfOption := SequencesV2.Seq_IndexOfOption
    Seq_LastIndexOf := SequencesV2.Seq_LastIndexOf
    Seq_LastIndexOfOption := SequencesV2.Seq_LastIndexOfOption
    Seq_Remove := SequencesV2.Seq_Remove
    Seq_RemoveValue := SequencesV2.Seq_RemoveValue
    Seq_Insert := SequencesV2.Seq_Insert
    Seq_Reverse := SequencesV2.Seq_Reverse
    Seq_Repeat := SequencesV2.Seq_Repeat
    Seq_Unzip := SequencesV2.Seq_Unzip
    Seq_Zip := SequencesV2.Seq_Zip
    Seq_Max := SequencesV2.Seq_Max
    Seq_Min := SequencesV2.Seq_Min
    Seq_Flatten := SequencesV2.Seq_Flatten
    Seq_FlattenReverse := SequencesV2.Seq_FlattenReverse
    Seq_Map := SequencesV2.Seq_Map
    Seq_MapWithResult := SequencesV2.Seq_MapWithResult
    Seq_Filter := SequencesV2.Seq_Filter
    Seq_FoldLeft := SequencesV2.Seq_FoldLeft
    Seq_FoldRight := SequencesV2.Seq_FoldRight
    Seq_FlatMap := SequencesV2.Seq_FlatMap
    Seq_MergeSort_MergeSortBy := SequencesV2.Seq_MergeSort_MergeSortBy
    Seq_MergeSort_MergeSortedWith := SequencesV2.Seq_MergeSort_MergeSortedWith
    LittleEndianNat_ToNatRight := SequencesV2.LittleEndianNat_ToNatRight
    LittleEndianNat_ToNatLeft := SequencesV2.LittleEndianNat_ToNatLeft
    LittleEndianNat_FromNat := SequencesV2.LittleEndianNat_FromNat
    LittleEndianNat_SeqExtend := SequencesV2.LittleEndianNat_SeqExtend
    LittleEndianNat_SeqExtendMultiple := SequencesV2.LittleEndianNat_SeqExtendMultiple
    LittleEndianNat_FromNatWithLen := SequencesV2.LittleEndianNat_FromNatWithLen
    LittleEndianNat_SeqZero := SequencesV2.LittleEndianNat_SeqZero
    LittleEndianNat_SeqAdd := SequencesV2.LittleEndianNat_SeqAdd
    LittleEndianNat_SeqSub := SequencesV2.LittleEndianNat_SeqSub
    LittleEndianNatConversions_ToSmall := SequencesV2.LittleEndianNatConversions_ToSmall
    LittleEndianNatConversions_ToLarge := SequencesV2.LittleEndianNatConversions_ToLarge
  }

/--
`joint_unsat spec_A spec_B [spec_C …] by <proof>` generates a theorem stating
that the requested specs cannot be satisfied simultaneously.
-/
syntax "joint_unsat" ident ident ident* "by" tacticSeq : command

open Lean in
macro_rules
  | `(joint_unsat $s1 $s2 $[$rest]* by $proof) => do
    let specs := #[s1, s2] ++ rest
    let name := specs.foldl (init := `joint_unsat) fun acc s => Name.append acc s.getId
    let mut body ← `($(specs[0]!) impl)
    for s in specs[1:] do
      body ← `($body ∧ $s impl)
    `(theorem $(mkIdent name) : ¬ ∃ impl : RepoImpl, $body := by $proof)
