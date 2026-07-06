-- !benchmark @start imports
-- !benchmark @end imports

/-!
# SequencesV2.Impl.Seq

Core sequence vocabulary, signatures, and reference implementations translated
from `Collections/Sequences/Seq.dfy`.

DO NOT MODIFY types or signatures. Implement only the function bodies inside
the `code` markers.
-/

namespace SequencesV2

-- Types

inductive Result (α ε : Type) where
  | Success (value : α)
  | Failure (error : ε)
  deriving Repr, DecidableEq, BEq

-- Frozen sequence helpers

def Seq_Count {T : Type} [DecidableEq T] (x : T) (xs : List T) : Nat :=
  (xs.filter (fun y => y = x)).length

def Seq_SameMultiset {T : Type} [DecidableEq T] (xs ys : List T) : Prop :=
  ∀ x : T, Seq_Count x xs = Seq_Count x ys

def Seq_Disjoint {T : Type} [DecidableEq T] (xs ys : List T) : Prop :=
  ∀ x : T, x ∈ xs → x ∈ ys → False

def Seq_Slice {T : Type} (xs : List T) (start stop : Nat) : List T :=
  (xs.drop start).take (stop - start)

def Seq_ToSet {T : Type} [DecidableEq T] (xs : List T) : List T :=
  xs.eraseDups

def Seq_HasNoDuplicates {T : Type} [DecidableEq T] (xs : List T) : Prop :=
  xs.Nodup

def Seq_InvFoldLeft {A B : Type} (inv : B → List A → Prop) (stp : B → A → B → Prop) : Prop :=
  ∀ (x : A) (xs : List A) (b b' : B), inv b (x :: xs) → stp b x b' → inv b' xs

def Seq_InvFoldRight {A B : Type} (inv : List A → B → Prop) (stp : A → B → B → Prop) : Prop :=
  ∀ (x : A) (xs : List A) (b b' : B), inv xs b → stp x b b' → inv (x :: xs) b'

-- API signatures

abbrev Seq_FirstSig := {T : Type} → (xs : List T) → xs.length > 0 → T
abbrev Seq_DropFirstSig := {T : Type} → (xs : List T) → xs.length > 0 → List T
abbrev Seq_LastSig := {T : Type} → (xs : List T) → xs.length > 0 → T
abbrev Seq_DropLastSig := {T : Type} → (xs : List T) → xs.length > 0 → List T
abbrev Seq_ToArraySig := {T : Type} → List T → Array T
abbrev Seq_IndexOfSig := {T : Type} → [DecidableEq T] → (xs : List T) → (v : T) → v ∈ xs → Nat
abbrev Seq_IndexOfOptionSig := {T : Type} → [DecidableEq T] → List T → T → Option Nat
abbrev Seq_LastIndexOfSig := {T : Type} → [DecidableEq T] → (xs : List T) → (v : T) → v ∈ xs → Nat
abbrev Seq_LastIndexOfOptionSig := {T : Type} → [DecidableEq T] → List T → T → Option Nat
abbrev Seq_RemoveSig := {T : Type} → (xs : List T) → (pos : Nat) → pos < xs.length → List T
abbrev Seq_RemoveValueSig := {T : Type} → [DecidableEq T] → List T → T → List T
abbrev Seq_InsertSig := {T : Type} → (xs : List T) → T → (pos : Nat) → pos ≤ xs.length → List T
abbrev Seq_ReverseSig := {T : Type} → List T → List T
abbrev Seq_RepeatSig := {T : Type} → T → Nat → List T
abbrev Seq_UnzipSig := {A B : Type} → List (A × B) → List A × List B
abbrev Seq_ZipSig := {A B : Type} → (xs : List A) → (ys : List B) → xs.length = ys.length → List (A × B)
abbrev Seq_MaxSig := (xs : List Int) → xs.length > 0 → Int
abbrev Seq_MinSig := (xs : List Int) → xs.length > 0 → Int
abbrev Seq_FlattenSig := {T : Type} → List (List T) → List T
abbrev Seq_FlattenReverseSig := {T : Type} → List (List T) → List T
abbrev Seq_MapSig := {T R : Type} → (T → R) → List T → List R
abbrev Seq_MapWithResultSig := {T R E : Type} → (T → Result R E) → List T → Result (List R) E
abbrev Seq_FilterSig := {T : Type} → (T → Bool) → List T → List T
abbrev Seq_FoldLeftSig := {A T : Type} → (A → T → A) → A → List T → A
abbrev Seq_FoldRightSig := {A T : Type} → (T → A → A) → List T → A → A
abbrev Seq_FlatMapSig := {T R : Type} → (T → List R) → List T → List R

end SequencesV2

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- !benchmark @start code_aux def=Seq_First
-- !benchmark @end code_aux def=Seq_First

def SequencesV2.Seq_First : SequencesV2.Seq_FirstSig :=
-- !benchmark @start code def=Seq_First
  fun xs h => xs.get ⟨0, h⟩
-- !benchmark @end code def=Seq_First

-- !benchmark @start code_aux def=Seq_DropFirst
-- !benchmark @end code_aux def=Seq_DropFirst

def SequencesV2.Seq_DropFirst : SequencesV2.Seq_DropFirstSig :=
-- !benchmark @start code def=Seq_DropFirst
  fun xs _h => xs.drop 1
-- !benchmark @end code def=Seq_DropFirst

-- !benchmark @start code_aux def=Seq_Last
-- !benchmark @end code_aux def=Seq_Last

def SequencesV2.Seq_Last : SequencesV2.Seq_LastSig :=
-- !benchmark @start code def=Seq_Last
  fun xs h => xs.get ⟨xs.length - 1, Nat.sub_lt h (by decide)⟩
-- !benchmark @end code def=Seq_Last

-- !benchmark @start code_aux def=Seq_DropLast
-- !benchmark @end code_aux def=Seq_DropLast

def SequencesV2.Seq_DropLast : SequencesV2.Seq_DropLastSig :=
-- !benchmark @start code def=Seq_DropLast
  fun xs _h => xs.take (xs.length - 1)
-- !benchmark @end code def=Seq_DropLast

-- !benchmark @start code_aux def=Seq_ToArray
-- !benchmark @end code_aux def=Seq_ToArray

def SequencesV2.Seq_ToArray : SequencesV2.Seq_ToArraySig :=
-- !benchmark @start code def=Seq_ToArray
  fun xs => xs.toArray
-- !benchmark @end code def=Seq_ToArray

-- !benchmark @start code_aux def=Seq_IndexOf
-- !benchmark @end code_aux def=Seq_IndexOf

def SequencesV2.Seq_IndexOf : SequencesV2.Seq_IndexOfSig :=
-- !benchmark @start code def=Seq_IndexOf
  fun xs v _h =>
    let rec go : List _ → Nat → Option Nat
      | [], _ => none
      | y :: ys, i => if y = v then some i else go ys (i + 1)
    match go xs 0 with
    | some i => i
    | none => 0
-- !benchmark @end code def=Seq_IndexOf

-- !benchmark @start code_aux def=Seq_IndexOfOption
-- !benchmark @end code_aux def=Seq_IndexOfOption

def SequencesV2.Seq_IndexOfOption : SequencesV2.Seq_IndexOfOptionSig :=
-- !benchmark @start code def=Seq_IndexOfOption
  fun xs v =>
    let rec go : List _ → Nat → Option Nat
      | [], _ => none
      | y :: ys, i => if y = v then some i else go ys (i + 1)
    go xs 0
-- !benchmark @end code def=Seq_IndexOfOption

-- !benchmark @start code_aux def=Seq_LastIndexOf
-- !benchmark @end code_aux def=Seq_LastIndexOf

def SequencesV2.Seq_LastIndexOf : SequencesV2.Seq_LastIndexOfSig :=
-- !benchmark @start code def=Seq_LastIndexOf
  fun xs v _h =>
    let rec go : List _ → Nat → Option Nat → Option Nat
      | [], _, last => last
      | y :: ys, i, last =>
          go ys (i + 1) (if y = v then some i else last)
    match go xs 0 none with
    | some i => i
    | none => 0
-- !benchmark @end code def=Seq_LastIndexOf

-- !benchmark @start code_aux def=Seq_LastIndexOfOption
-- !benchmark @end code_aux def=Seq_LastIndexOfOption

def SequencesV2.Seq_LastIndexOfOption : SequencesV2.Seq_LastIndexOfOptionSig :=
-- !benchmark @start code def=Seq_LastIndexOfOption
  fun xs v =>
    let rec go : List _ → Nat → Option Nat → Option Nat
      | [], _, last => last
      | y :: ys, i, last =>
          go ys (i + 1) (if y = v then some i else last)
    go xs 0 none
-- !benchmark @end code def=Seq_LastIndexOfOption

-- !benchmark @start code_aux def=Seq_Remove
-- !benchmark @end code_aux def=Seq_Remove

def SequencesV2.Seq_Remove : SequencesV2.Seq_RemoveSig :=
-- !benchmark @start code def=Seq_Remove
  fun xs pos _h => xs.take pos ++ xs.drop (pos + 1)
-- !benchmark @end code def=Seq_Remove

-- !benchmark @start code_aux def=Seq_RemoveValue
-- !benchmark @end code_aux def=Seq_RemoveValue

def SequencesV2.Seq_RemoveValue : SequencesV2.Seq_RemoveValueSig :=
-- !benchmark @start code def=Seq_RemoveValue
  fun xs v => xs.erase v
-- !benchmark @end code def=Seq_RemoveValue

-- !benchmark @start code_aux def=Seq_Insert
-- !benchmark @end code_aux def=Seq_Insert

def SequencesV2.Seq_Insert : SequencesV2.Seq_InsertSig :=
-- !benchmark @start code def=Seq_Insert
  fun xs a pos _h => xs.take pos ++ [a] ++ xs.drop pos
-- !benchmark @end code def=Seq_Insert

-- !benchmark @start code_aux def=Seq_Reverse
-- !benchmark @end code_aux def=Seq_Reverse

def SequencesV2.Seq_Reverse : SequencesV2.Seq_ReverseSig :=
-- !benchmark @start code def=Seq_Reverse
  fun xs => xs.reverse
-- !benchmark @end code def=Seq_Reverse

-- !benchmark @start code_aux def=Seq_Repeat
-- !benchmark @end code_aux def=Seq_Repeat

def SequencesV2.Seq_Repeat : SequencesV2.Seq_RepeatSig :=
-- !benchmark @start code def=Seq_Repeat
  fun v length => List.replicate length v
-- !benchmark @end code def=Seq_Repeat

-- !benchmark @start code_aux def=Seq_Unzip
-- !benchmark @end code_aux def=Seq_Unzip

def SequencesV2.Seq_Unzip : SequencesV2.Seq_UnzipSig :=
-- !benchmark @start code def=Seq_Unzip
  fun xs => xs.foldr (fun p acc => (p.1 :: acc.1, p.2 :: acc.2)) ([], [])
-- !benchmark @end code def=Seq_Unzip

-- !benchmark @start code_aux def=Seq_Zip
-- !benchmark @end code_aux def=Seq_Zip

def SequencesV2.Seq_Zip : SequencesV2.Seq_ZipSig :=
-- !benchmark @start code def=Seq_Zip
  fun xs ys _h => List.zip xs ys
-- !benchmark @end code def=Seq_Zip

-- !benchmark @start code_aux def=Seq_Max
-- !benchmark @end code_aux def=Seq_Max

def SequencesV2.Seq_Max : SequencesV2.Seq_MaxSig :=
-- !benchmark @start code def=Seq_Max
  fun xs h =>
    match xs with
    | [] => False.elim ((Nat.lt_irrefl 0) h)
    | x :: rest => rest.foldl max x
-- !benchmark @end code def=Seq_Max

-- !benchmark @start code_aux def=Seq_Min
-- !benchmark @end code_aux def=Seq_Min

def SequencesV2.Seq_Min : SequencesV2.Seq_MinSig :=
-- !benchmark @start code def=Seq_Min
  fun xs h =>
    match xs with
    | [] => False.elim ((Nat.lt_irrefl 0) h)
    | x :: rest => rest.foldl min x
-- !benchmark @end code def=Seq_Min

-- !benchmark @start code_aux def=Seq_Flatten
-- !benchmark @end code_aux def=Seq_Flatten

def SequencesV2.Seq_Flatten : SequencesV2.Seq_FlattenSig :=
-- !benchmark @start code def=Seq_Flatten
  fun xs => xs.flatten
-- !benchmark @end code def=Seq_Flatten

-- !benchmark @start code_aux def=Seq_FlattenReverse
-- !benchmark @end code_aux def=Seq_FlattenReverse

def SequencesV2.Seq_FlattenReverse : SequencesV2.Seq_FlattenReverseSig :=
-- !benchmark @start code def=Seq_FlattenReverse
  fun xs => xs.flatten
-- !benchmark @end code def=Seq_FlattenReverse

-- !benchmark @start code_aux def=Seq_Map
-- !benchmark @end code_aux def=Seq_Map

def SequencesV2.Seq_Map : SequencesV2.Seq_MapSig :=
-- !benchmark @start code def=Seq_Map
  fun f xs => xs.map f
-- !benchmark @end code def=Seq_Map

-- !benchmark @start code_aux def=Seq_MapWithResult
-- !benchmark @end code_aux def=Seq_MapWithResult

def SequencesV2.Seq_MapWithResult : SequencesV2.Seq_MapWithResultSig :=
-- !benchmark @start code def=Seq_MapWithResult
  fun f xs =>
    let rec go : List _ → SequencesV2.Result (List _) _
      | [] => SequencesV2.Result.Success []
      | x :: rest =>
          match f x with
          | SequencesV2.Result.Failure e => SequencesV2.Result.Failure e
          | SequencesV2.Result.Success y =>
              match go rest with
              | SequencesV2.Result.Failure e => SequencesV2.Result.Failure e
              | SequencesV2.Result.Success ys => SequencesV2.Result.Success (y :: ys)
    go xs
-- !benchmark @end code def=Seq_MapWithResult

-- !benchmark @start code_aux def=Seq_Filter
-- !benchmark @end code_aux def=Seq_Filter

def SequencesV2.Seq_Filter : SequencesV2.Seq_FilterSig :=
-- !benchmark @start code def=Seq_Filter
  fun f xs => xs.filter f
-- !benchmark @end code def=Seq_Filter

-- !benchmark @start code_aux def=Seq_FoldLeft
-- !benchmark @end code_aux def=Seq_FoldLeft

def SequencesV2.Seq_FoldLeft : SequencesV2.Seq_FoldLeftSig :=
-- !benchmark @start code def=Seq_FoldLeft
  fun f init xs => xs.foldl f init
-- !benchmark @end code def=Seq_FoldLeft

-- !benchmark @start code_aux def=Seq_FoldRight
-- !benchmark @end code_aux def=Seq_FoldRight

def SequencesV2.Seq_FoldRight : SequencesV2.Seq_FoldRightSig :=
-- !benchmark @start code def=Seq_FoldRight
  fun f xs init => xs.foldr f init
-- !benchmark @end code def=Seq_FoldRight

-- !benchmark @start code_aux def=Seq_FlatMap
-- !benchmark @end code_aux def=Seq_FlatMap

def SequencesV2.Seq_FlatMap : SequencesV2.Seq_FlatMapSig :=
-- !benchmark @start code def=Seq_FlatMap
  fun f xs => xs.flatMap f
-- !benchmark @end code def=Seq_FlatMap
