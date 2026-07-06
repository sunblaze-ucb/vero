import Eth20Dafny.Impl.SszBytesAndBits

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Eth20Dafny.Impl.SszBitVectorSeDes

SSZ bitvector serialization and deserialization translated from
`ssz/BitVectorSeDes.dfy`.

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
Implement only the function bodies.
-/

-- !benchmark @start global_aux
-- !benchmark @end global_aux

namespace Eth20Dafny

-- API signatures.
abbrev FromBitvectorToBytesSig := List Bool → List UInt8
abbrev FromBytesToBitVectorSig := List UInt8 → Nat → List Bool

/-- Source-backed helper predicate from `BitVectorSeDes.isValidBitVectorEncoding`. -/
def isValidBitVectorEncoding (xb : List UInt8) (len : Nat) : Prop :=
  0 < xb.length ∧ xb.length = (len + 7) / 8

end Eth20Dafny

-- !benchmark @start code_aux def=fromBitvectorToBytes
-- !benchmark @end code_aux def=fromBitvectorToBytes

def Eth20Dafny.fromBitvectorToBytes : Eth20Dafny.FromBitvectorToBytesSig :=
-- !benchmark @start code def=fromBitvectorToBytes
  let rec go : Nat → List Bool → List UInt8
    | 0, _ => []
    | fuel + 1, bits =>
      if bits.length ≤ 8 then
        [list8BitsToByte (bits ++ List.replicate (8 - bits.length) false)]
      else
        let chunk := bits.take 8
        list8BitsToByte chunk :: go fuel (bits.drop 8)
  fun l => go l.length l
-- !benchmark @end code def=fromBitvectorToBytes

-- !benchmark @start code_aux def=fromBytesToBitVector
-- !benchmark @end code_aux def=fromBytesToBitVector

def Eth20Dafny.fromBytesToBitVector : Eth20Dafny.FromBytesToBitVectorSig :=
-- !benchmark @start code def=fromBytesToBitVector
  let rec go : List UInt8 → Nat → List Bool
    | [], _ => []
    | x :: [], len => (byteTo8Bits x).take len
    | x :: xs, len => byteTo8Bits x ++ go xs (len - 8)
  fun xb len => go xb len
-- !benchmark @end code def=fromBytesToBitVector
