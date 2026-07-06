import SequencesV2.Impl.Seq
import SequencesV2.Impl.MergeSort
import SequencesV2.Impl.LittleEndianNat
import SequencesV2.Impl.LittleEndianNatConversions

/-!
# SequencesV2.Test

Executable conformance tests against the curated reference implementations
inside the `Impl/*.lean` `code` markers.

DO NOT MODIFY — benchmark infrastructure.
-/

open SequencesV2

#guard Seq_First [1, 2, 3] (by decide) == 1
#guard Seq_DropFirst [1, 2, 3] (by decide) == [2, 3]
#guard Seq_Last [1, 2, 3] (by decide) == 3
#guard Seq_DropLast [1, 2, 3] (by decide) == [1, 2]
#guard Seq_IndexOf [4, 5, 4] 4 (by decide) == 0
#guard Seq_IndexOfOption [4, 5, 4] 4 == some 0
#guard Seq_IndexOfOption [4, 5, 4] 7 == none
#guard Seq_LastIndexOf [4, 5, 4] 4 (by decide) == 2
#guard Seq_LastIndexOfOption [4, 5, 4] 4 == some 2
#guard Seq_LastIndexOfOption [4, 5, 4] 7 == none
#guard Seq_Insert [1, 3] 2 1 (by decide) == [1, 2, 3]
#guard Seq_Remove [1, 2, 3] 1 (by decide) == [1, 3]
#guard Seq_RemoveValue [1, 2, 1, 3] 1 == [2, 1, 3]
#guard Seq_Reverse [1, 2, 3] == [3, 2, 1]
#guard Seq_Unzip (Seq_Zip [1, 2] [3, 4] (by decide)) == ([1, 2], [3, 4])
#guard Seq_Repeat true 3 == [true, true, true]
#guard Seq_Max [(-3 : Int), 7, 2] (by decide) == 7
#guard Seq_Min [(-3 : Int), 7, 2] (by decide) == -3
#guard Seq_Flatten [[1, 2], [], [3]] == [1, 2, 3]
#guard Seq_FlattenReverse [[1, 2], [], [3]] == [1, 2, 3]
#guard Seq_Map (fun x : Nat => x + 1) [1, 2, 3] == [2, 3, 4]
#guard Seq_MapWithResult
    (fun x : Nat => if x < 3 then Result.Success (x + 10) else Result.Failure 99)
    [1, 2] == Result.Success [11, 12]
#guard Seq_MapWithResult
    (fun x : Nat => if x < 3 then Result.Success (x + 10) else Result.Failure 99)
    [1, 3, 2] == Result.Failure 99
#guard (Seq_ToArray [1, 2, 3]).toList == [1, 2, 3]
#guard Seq_FoldLeft (fun acc x : Nat => acc - x) 10 [1, 2, 3] == 4
#guard Seq_FoldRight (fun x acc : Nat => x - acc) [10, 3, 1] 0 == 8
#guard Seq_FlatMap (fun x : Nat => [x, x + 10]) [1, 2] == [1, 11, 2, 12]
#guard Seq_Filter (fun x : Nat => decide (x % 2 = 0)) [1, 2, 3, 4] == [2, 4]
#guard
  Seq_MergeSort_MergeSortBy [3, 1, 2]
      (fun x y : Nat => decide (x ≤ y))
      (by
        constructor
        · intro x
          simp
        constructor
        · intro x y
          by_cases h : x ≤ y
          · left
            simp [h]
          · right
            have hyx : y ≤ x := Nat.le_of_not_ge h
            simp [hyx]
        · intro x y z hxy hyz
          simp at hxy hyz ⊢
          exact Nat.le_trans hxy hyz) == [1, 2, 3]
#guard
  Seq_MergeSort_MergeSortedWith [1, 3] [2, 4]
      (fun _ _ : Nat => true)
      (by
        intro i j _hij _hj
        split <;> trivial)
      (by
        intro i j _hij _hj
        split <;> trivial)
      (by
        constructor
        · intro x
          rfl
        constructor
        · intro x y
          left
          rfl
        · intro x y z _hxy _hyz
          rfl) == [1, 3, 2, 4]
#guard LittleEndianNat_FromNat LittleEndianNat_uint8Model 0 == []
#guard LittleEndianNat_ToNatRight LittleEndianNat_uint8Model [1, 2] == 513
#guard LittleEndianNat_ToNatLeft LittleEndianNat_uint8Model [1, 2] == 513
#guard LittleEndianNat_FromNat LittleEndianNat_uint8Model 513 == [1, 2]
#guard LittleEndianNat_SeqExtend LittleEndianNat_uint8Model [5] 3 (by decide) == [5, 0, 0]
#guard LittleEndianNat_SeqExtendMultiple LittleEndianNat_uint8Model [5, 6] 4 (by decide) == [5, 6, 0, 0]
#guard LittleEndianNat_FromNatWithLen LittleEndianNat_uint8Model 513 3 (by decide) == [1, 2, 0]
#guard LittleEndianNat_SeqZero LittleEndianNat_uint8Model 3 == [0, 0, 0]
#guard LittleEndianNat_SeqAdd LittleEndianNat_uint8Model [1, 0] [2, 0] (by decide) == ([3, 0], 0)
#guard LittleEndianNat_SeqSub LittleEndianNat_uint8Model [5, 1] [3, 0] (by decide) == ([2, 1], 0)
#guard LittleEndianNatConversions_ToSmall LittleEndianNatConversions_uint8_16Model [513] == [1, 2]
#guard LittleEndianNatConversions_ToLarge LittleEndianNatConversions_uint8_16Model [1, 2] (by decide) == [513]
