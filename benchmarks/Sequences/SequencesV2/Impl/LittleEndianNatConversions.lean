import SequencesV2.Impl.Trusted
import SequencesV2.Impl.Seq

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# SequencesV2.Impl.LittleEndianNatConversions

Little-endian natural-number conversions between small-base and large-base
digit sequences translated from `Collections/Sequences/LittleEndianNatConversions.dfy`.
Types and signatures are fixed vocabulary (DO NOT MODIFY). Function bodies are
the curator's reference implementations inside the `code` markers.
-/

namespace SequencesV2

-- Types

structure LittleEndianNatConversions_Model where
  smallBits : Nat
  smallBits_gt_one : smallBits > 1
  largeBits : Nat
  largeBits_gt_smallBits : largeBits > smallBits
  largeBits_mod_smallBits : largeBits % smallBits = 0
  e_pow : PowNat (PowNat 2 smallBits) (largeBits / smallBits) = PowNat 2 largeBits
  e_pos : largeBits / smallBits > 0

abbrev Small_uint := Nat

abbrev Large_uint := Nat

-- Frozen semantic helpers

def SmallSeq_BITS (model : LittleEndianNatConversions_Model) : Nat :=
  model.smallBits

def BITS (model : LittleEndianNatConversions_Model) : Nat :=
  SmallSeq_BITS model

def SmallSeq_BASE (model : LittleEndianNatConversions_Model) : Nat :=
  PowNat 2 (SmallSeq_BITS model)

def LargeSeq_BITS (model : LittleEndianNatConversions_Model) : Nat :=
  model.largeBits

def LargeSeq_BASE (model : LittleEndianNatConversions_Model) : Nat :=
  PowNat 2 (LargeSeq_BITS model)

def LittleEndianNatConversions_E (model : LittleEndianNatConversions_Model) : Nat :=
  LargeSeq_BITS model / SmallSeq_BITS model

def Small_isUint (model : LittleEndianNatConversions_Model) (x : Small_uint) : Prop :=
  x < SmallSeq_BASE model

def Large_isUint (model : LittleEndianNatConversions_Model) (x : Large_uint) : Prop :=
  x < LargeSeq_BASE model

def Small_validSeq (model : LittleEndianNatConversions_Model) (xs : List Small_uint) : Prop :=
  ∀ x, x ∈ xs → Small_isUint model x

def Large_validSeq (model : LittleEndianNatConversions_Model) (xs : List Large_uint) : Prop :=
  ∀ x, x ∈ xs → Large_isUint model x

def Small_ToNatRight (model : LittleEndianNatConversions_Model) (xs : List Small_uint) : Nat :=
  xs.foldr (fun x acc => acc * (SmallSeq_BASE model) + x) 0

def Large_ToNatRight (model : LittleEndianNatConversions_Model) (xs : List Large_uint) : Nat :=
  xs.foldr (fun x acc => acc * (LargeSeq_BASE model) + x) 0

def Small_FromNatWithLen
    (model : LittleEndianNatConversions_Model) (n len : Nat)
    (_h : PowNat (SmallSeq_BASE model) len > n) : List Small_uint :=
  (List.range len).map (fun i => (n / PowNat (SmallSeq_BASE model) i) % (SmallSeq_BASE model))

def LittleEndianNatConversions_uint8_16Model : LittleEndianNatConversions_Model where
  smallBits := 8
  smallBits_gt_one := by decide
  largeBits := 16
  largeBits_gt_smallBits := by decide
  largeBits_mod_smallBits := by decide
  e_pow := by decide
  e_pos := by decide

-- API signatures

abbrev LittleEndianNatConversions_ToSmallSig :=
  (model : LittleEndianNatConversions_Model) → List Large_uint → List Small_uint

abbrev LittleEndianNatConversions_ToLargeSig :=
  (model : LittleEndianNatConversions_Model) → (xs : List Small_uint) →
    xs.length % (LittleEndianNatConversions_E model) = 0 → List Large_uint

end SequencesV2

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- !benchmark @start code_aux def=LittleEndianNatConversions_ToSmall
-- !benchmark @end code_aux def=LittleEndianNatConversions_ToSmall

def SequencesV2.LittleEndianNatConversions_ToSmall :
    SequencesV2.LittleEndianNatConversions_ToSmallSig :=
-- !benchmark @start code def=LittleEndianNatConversions_ToSmall
  fun model xs =>
    xs.flatMap (fun x =>
      (List.range (SequencesV2.LittleEndianNatConversions_E model)).map
        (fun i =>
          (x / SequencesV2.PowNat (SequencesV2.SmallSeq_BASE model) i) %
            SequencesV2.SmallSeq_BASE model))
-- !benchmark @end code def=LittleEndianNatConversions_ToSmall

-- !benchmark @start code_aux def=LittleEndianNatConversions_ToLarge
-- !benchmark @end code_aux def=LittleEndianNatConversions_ToLarge

def SequencesV2.LittleEndianNatConversions_ToLarge :
    SequencesV2.LittleEndianNatConversions_ToLargeSig :=
-- !benchmark @start code def=LittleEndianNatConversions_ToLarge
  fun model xs _h =>
    (List.range (xs.length / SequencesV2.LittleEndianNatConversions_E model)).map
      (fun chunk =>
        SequencesV2.Small_ToNatRight model
          (SequencesV2.Seq_Slice xs
            (chunk * SequencesV2.LittleEndianNatConversions_E model)
            ((chunk + 1) * SequencesV2.LittleEndianNatConversions_E model)))
-- !benchmark @end code def=LittleEndianNatConversions_ToLarge
