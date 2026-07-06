import Eth20Dafny.Impl.SszBytesAndBits

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Eth20Dafny.Impl.SszBitListSeDes

Bit list serialization and deserialization helpers translated from
`ssz/BitListSeDes.dfy`.

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
Implement only the reference implementations.
-/

-- !benchmark @start global_aux
-- !benchmark @end global_aux

namespace Eth20Dafny

abbrev LargestIndexOfOneSig := List Bool → Nat
abbrev FromBitlistToBytesSig := List Bool → List UInt8
abbrev FromBytesToBitListSig := List UInt8 → List Bool

end Eth20Dafny

-- !benchmark @start code_aux def=largestIndexOfOne
-- !benchmark @end code_aux def=largestIndexOfOne

def Eth20Dafny.largestIndexOfOne : Eth20Dafny.LargestIndexOfOneSig :=
-- !benchmark @start code def=largestIndexOfOne
  fun l =>
    if l.getD 7 false then 7
    else if l.getD 6 false then 6
    else if l.getD 5 false then 5
    else if l.getD 4 false then 4
    else if l.getD 3 false then 3
    else if l.getD 2 false then 2
    else if l.getD 1 false then 1
    else 0
-- !benchmark @end code def=largestIndexOfOne

-- !benchmark @start code_aux def=fromBitlistToBytes
-- !benchmark @end code_aux def=fromBitlistToBytes

def Eth20Dafny.fromBitlistToBytes : Eth20Dafny.FromBitlistToBytesSig :=
-- !benchmark @start code def=fromBitlistToBytes
  fun l => fromBitsToBytes (l ++ [true])
-- !benchmark @end code def=fromBitlistToBytes

-- !benchmark @start code_aux def=fromBytesToBitList
-- !benchmark @end code_aux def=fromBytesToBitList

def Eth20Dafny.fromBytesToBitList : Eth20Dafny.FromBytesToBitListSig :=
-- !benchmark @start code def=fromBytesToBitList
  let rec go : List UInt8 → List Bool
    | [] => []
    | [x] =>
      let bits := byteTo8Bits x
      bits.take (largestIndexOfOne bits)
    | x :: xs => byteTo8Bits x ++ go xs
  go
-- !benchmark @end code def=fromBytesToBitList
