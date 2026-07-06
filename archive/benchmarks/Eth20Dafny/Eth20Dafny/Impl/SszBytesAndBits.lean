-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Eth20Dafny.Impl.SszBytesAndBits

Helpers for converting booleans and bytes.

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
Implement only the function bodies.
-/

-- !benchmark @start global_aux
-- !benchmark @end global_aux

namespace Eth20Dafny

abbrev BoolToByteSig := Bool → UInt8
abbrev BytesAndBitsByteToBoolSig := UInt8 → Bool
abbrev List8BitsToByteSig := List Bool → UInt8
abbrev ByteTo8BitsSig := UInt8 → List Bool
abbrev FromBitsToBytesSig := List Bool → List UInt8

end Eth20Dafny

-- !benchmark @start code_aux def=boolToByte
-- !benchmark @end code_aux def=boolToByte

def Eth20Dafny.boolToByte : Eth20Dafny.BoolToByteSig :=
-- !benchmark @start code def=boolToByte
  fun b => if b then (1 : UInt8) else (0 : UInt8)
-- !benchmark @end code def=boolToByte

-- !benchmark @start code_aux def=bytesAndBitsByteToBool
-- !benchmark @end code_aux def=bytesAndBitsByteToBool

def Eth20Dafny.bytesAndBitsByteToBool : Eth20Dafny.BytesAndBitsByteToBoolSig :=
-- !benchmark @start code def=bytesAndBitsByteToBool
  fun b => b.toNat == 1
-- !benchmark @end code def=bytesAndBitsByteToBool

-- !benchmark @start code_aux def=list8BitsToByte
-- !benchmark @end code_aux def=list8BitsToByte

def Eth20Dafny.list8BitsToByte : Eth20Dafny.List8BitsToByteSig :=
-- !benchmark @start code def=list8BitsToByte
  fun l =>
    let bit (i : Nat) : Nat := if l.getD i false then 1 else 0
    UInt8.ofNat
      (128 * bit 7 +
       64 * bit 6 +
       32 * bit 5 +
       16 * bit 4 +
       8 * bit 3 +
       4 * bit 2 +
       2 * bit 1 +
       bit 0)
-- !benchmark @end code def=list8BitsToByte

-- !benchmark @start code_aux def=byteTo8Bits
-- !benchmark @end code_aux def=byteTo8Bits

def Eth20Dafny.byteTo8Bits : Eth20Dafny.ByteTo8BitsSig :=
-- !benchmark @start code def=byteTo8Bits
  fun n =>
    let natVal := n.toNat
    [
      ((natVal / 1) % 2) == 1,
      ((natVal / 2) % 2) == 1,
      ((natVal / 4) % 2) == 1,
      ((natVal / 8) % 2) == 1,
      ((natVal / 16) % 2) == 1,
      ((natVal / 32) % 2) == 1,
      ((natVal / 64) % 2) == 1,
      ((natVal / 128) % 2) == 1
    ]
-- !benchmark @end code def=byteTo8Bits

-- !benchmark @start code_aux def=fromBitsToBytes
-- !benchmark @end code_aux def=fromBitsToBytes

def Eth20Dafny.fromBitsToBytes : Eth20Dafny.FromBitsToBytesSig :=
-- !benchmark @start code def=fromBitsToBytes
  fun l =>
    let rec go : Nat → List Bool → List UInt8
      | 0, _ => []
      | fuel + 1, bits =>
        if bits.isEmpty then
          []
        else
          let chunk := bits.take 8
          let paddedChunk := chunk ++ List.replicate (8 - chunk.length) false
          let byte := list8BitsToByte paddedChunk
          if bits.length ≤ 8 then
            [byte]
          else
            byte :: go fuel (bits.drop 8)
    go l.length l
-- !benchmark @end code def=fromBitsToBytes
