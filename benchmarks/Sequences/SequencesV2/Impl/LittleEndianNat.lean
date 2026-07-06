import SequencesV2.Impl.Seq
import SequencesV2.Impl.Trusted

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# SequencesV2.Impl.LittleEndianNat

Little-endian natural-number sequence operations translated from
`Collections/Sequences/LittleEndianNat.dfy`. Types and signatures are fixed
vocabulary (DO NOT MODIFY). Function bodies are the curator's reference
implementations inside the `code` markers.
-/

namespace SequencesV2

-- Types

structure LittleEndianNat_Model where
  base : Nat
  base_gt_one : base > 1

abbrev LittleEndianNat_uint := Nat

-- Frozen semantic helpers

def LittleEndianNat_BASE (model : LittleEndianNat_Model) : Nat :=
  model.base

def LittleEndianNat_isUint (model : LittleEndianNat_Model) (x : LittleEndianNat_uint) : Prop :=
  x < LittleEndianNat_BASE model

def LittleEndianNat_validSeq (model : LittleEndianNat_Model) (xs : List LittleEndianNat_uint) : Prop :=
  ∀ x, x ∈ xs → LittleEndianNat_isUint model x

def LittleEndianNat_uint8Model : LittleEndianNat_Model where
  base := 256
  base_gt_one := by decide

-- API signatures

abbrev LittleEndianNat_ToNatRightSig :=
  (model : LittleEndianNat_Model) → List LittleEndianNat_uint → Nat

abbrev LittleEndianNat_ToNatLeftSig :=
  (model : LittleEndianNat_Model) → List LittleEndianNat_uint → Nat

abbrev LittleEndianNat_FromNatSig :=
  (model : LittleEndianNat_Model) → Nat → List LittleEndianNat_uint

abbrev LittleEndianNat_SeqExtendSig :=
  (model : LittleEndianNat_Model) → (xs : List LittleEndianNat_uint) →
    (n : Nat) → xs.length ≤ n → List LittleEndianNat_uint

abbrev LittleEndianNat_SeqExtendMultipleSig :=
  (model : LittleEndianNat_Model) → (xs : List LittleEndianNat_uint) →
    (n : Nat) → n > 0 → List LittleEndianNat_uint

abbrev LittleEndianNat_FromNatWithLenSig :=
  (model : LittleEndianNat_Model) → (n len : Nat) →
    PowNat (LittleEndianNat_BASE model) len > n → List LittleEndianNat_uint

abbrev LittleEndianNat_SeqZeroSig :=
  (model : LittleEndianNat_Model) → Nat → List LittleEndianNat_uint

abbrev LittleEndianNat_SeqAddSig :=
  (model : LittleEndianNat_Model) → (xs ys : List LittleEndianNat_uint) →
    xs.length = ys.length → List LittleEndianNat_uint × Nat

abbrev LittleEndianNat_SeqSubSig :=
  (model : LittleEndianNat_Model) → (xs ys : List LittleEndianNat_uint) →
    xs.length = ys.length → List LittleEndianNat_uint × Nat

end SequencesV2

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- !benchmark @start code_aux def=LittleEndianNat_ToNatRight
-- !benchmark @end code_aux def=LittleEndianNat_ToNatRight

def SequencesV2.LittleEndianNat_ToNatRight : SequencesV2.LittleEndianNat_ToNatRightSig :=
-- !benchmark @start code def=LittleEndianNat_ToNatRight
  fun model xs =>
    let base := SequencesV2.LittleEndianNat_BASE model
    xs.foldr (fun x acc => acc * base + x) 0
-- !benchmark @end code def=LittleEndianNat_ToNatRight

-- !benchmark @start code_aux def=LittleEndianNat_ToNatLeft
-- !benchmark @end code_aux def=LittleEndianNat_ToNatLeft

def SequencesV2.LittleEndianNat_ToNatLeft : SequencesV2.LittleEndianNat_ToNatLeftSig :=
-- !benchmark @start code def=LittleEndianNat_ToNatLeft
  fun model xs =>
    let base := SequencesV2.LittleEndianNat_BASE model
    xs.reverse.foldl (fun acc x => acc * base + x) 0
-- !benchmark @end code def=LittleEndianNat_ToNatLeft

-- !benchmark @start code_aux def=LittleEndianNat_FromNat
-- !benchmark @end code_aux def=LittleEndianNat_FromNat

def SequencesV2.LittleEndianNat_FromNat : SequencesV2.LittleEndianNat_FromNatSig :=
-- !benchmark @start code def=LittleEndianNat_FromNat
  fun model n =>
    let base := SequencesV2.LittleEndianNat_BASE model
    let rec go : Nat → Nat → List SequencesV2.LittleEndianNat_uint
      | 0, _ => []
      | fuel + 1, value =>
          if value = 0 then
            []
          else
            (value % base) :: go fuel (value / base)
    go (n + 1) n
-- !benchmark @end code def=LittleEndianNat_FromNat

-- !benchmark @start code_aux def=LittleEndianNat_SeqExtend
-- !benchmark @end code_aux def=LittleEndianNat_SeqExtend

def SequencesV2.LittleEndianNat_SeqExtend : SequencesV2.LittleEndianNat_SeqExtendSig :=
-- !benchmark @start code def=LittleEndianNat_SeqExtend
  fun _model xs n _h =>
    xs ++ List.replicate (n - xs.length) 0
-- !benchmark @end code def=LittleEndianNat_SeqExtend

-- !benchmark @start code_aux def=LittleEndianNat_SeqExtendMultiple
-- !benchmark @end code_aux def=LittleEndianNat_SeqExtendMultiple

def SequencesV2.LittleEndianNat_SeqExtendMultiple : SequencesV2.LittleEndianNat_SeqExtendMultipleSig :=
-- !benchmark @start code def=LittleEndianNat_SeqExtendMultiple
  fun _model xs n _h =>
    let newLen := xs.length + n - (xs.length % n)
    xs ++ List.replicate (newLen - xs.length) 0
-- !benchmark @end code def=LittleEndianNat_SeqExtendMultiple

-- !benchmark @start code_aux def=LittleEndianNat_FromNatWithLen
-- !benchmark @end code_aux def=LittleEndianNat_FromNatWithLen

def SequencesV2.LittleEndianNat_FromNatWithLen : SequencesV2.LittleEndianNat_FromNatWithLenSig :=
-- !benchmark @start code def=LittleEndianNat_FromNatWithLen
  fun model n len _h =>
    let base := SequencesV2.LittleEndianNat_BASE model
    let rec go : Nat → Nat → List SequencesV2.LittleEndianNat_uint
      | 0, _ => []
      | fuel + 1, value =>
          (value % base) :: go fuel (value / base)
    go len n
-- !benchmark @end code def=LittleEndianNat_FromNatWithLen

-- !benchmark @start code_aux def=LittleEndianNat_SeqZero
-- !benchmark @end code_aux def=LittleEndianNat_SeqZero

def SequencesV2.LittleEndianNat_SeqZero : SequencesV2.LittleEndianNat_SeqZeroSig :=
-- !benchmark @start code def=LittleEndianNat_SeqZero
  fun _model len =>
    List.replicate len 0
-- !benchmark @end code def=LittleEndianNat_SeqZero

-- !benchmark @start code_aux def=LittleEndianNat_SeqAdd
-- !benchmark @end code_aux def=LittleEndianNat_SeqAdd

def SequencesV2.LittleEndianNat_SeqAdd : SequencesV2.LittleEndianNat_SeqAddSig :=
-- !benchmark @start code def=LittleEndianNat_SeqAdd
  fun model xs ys _h =>
    let base := SequencesV2.LittleEndianNat_BASE model
    let rec go : List SequencesV2.LittleEndianNat_uint →
        List SequencesV2.LittleEndianNat_uint → Nat →
        List SequencesV2.LittleEndianNat_uint × Nat
      | [], _, carry => ([], carry)
      | _, [], carry => ([], carry)
      | x :: xs', y :: ys', carry =>
          let sum := x + y + carry
          let digit := if sum < base then sum else sum - base
          let carry' := if sum < base then 0 else 1
          let r := go xs' ys' carry'
          (digit :: r.1, r.2)
    go xs ys 0
-- !benchmark @end code def=LittleEndianNat_SeqAdd

-- !benchmark @start code_aux def=LittleEndianNat_SeqSub
-- !benchmark @end code_aux def=LittleEndianNat_SeqSub

def SequencesV2.LittleEndianNat_SeqSub : SequencesV2.LittleEndianNat_SeqSubSig :=
-- !benchmark @start code def=LittleEndianNat_SeqSub
  fun model xs ys _h =>
    let base := SequencesV2.LittleEndianNat_BASE model
    let rec go : List SequencesV2.LittleEndianNat_uint →
        List SequencesV2.LittleEndianNat_uint → Nat →
        List SequencesV2.LittleEndianNat_uint × Nat
      | [], _, borrow => ([], borrow)
      | _, [], borrow => ([], borrow)
      | x :: xs', y :: ys', borrow =>
          let subtrahend := y + borrow
          let digit := if subtrahend ≤ x then x - subtrahend else base + x - subtrahend
          let borrow' := if subtrahend ≤ x then 0 else 1
          let r := go xs' ys' borrow'
          (digit :: r.1, r.2)
    go xs ys 0
-- !benchmark @end code def=LittleEndianNat_SeqSub
