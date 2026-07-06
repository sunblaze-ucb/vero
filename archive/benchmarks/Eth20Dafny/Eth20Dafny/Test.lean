import Eth20Dafny.Impl.SszBitListSeDes
import Eth20Dafny.Impl.SszBitVectorSeDes
import Eth20Dafny.Impl.SszBoolSeDes
import Eth20Dafny.Impl.SszBytesAndBits
import Eth20Dafny.Impl.SszIntSeDes
import Eth20Dafny.Impl.SszSerialise
import Eth20Dafny.Impl.Utils.Eth2Types
import Eth20Dafny.Impl.Utils.Nativetypes
import Eth20Dafny.Impl.Utils.Nonnativetypes
import Eth20Dafny.Impl.UtilsEth2Types
import Eth20Dafny.Impl.UtilsHelpers
import Eth20Dafny.Impl.UtilsMathHelpers

/-!
# Eth20Dafny.Test

Executable conformance checks for the curated implementation references.
*-/

#guard Eth20Dafny.boolToByte true == UInt8.ofNat 1
#guard Eth20Dafny.bytesAndBitsByteToBool (UInt8.ofNat 1) == true
#guard Eth20Dafny.list8BitsToByte [true, false, false, false, false, false, false, false] == UInt8.ofNat 1
#guard Eth20Dafny.byteTo8Bits (UInt8.ofNat 5) == [true, false, true, false, false, false, false, false]
#guard Eth20Dafny.uintDes (Eth20Dafny.uintSe 42 1) == 42
#guard Eth20Dafny.get_next_power_of_two 5 == 8
#guard Eth20Dafny.get_prev_power_of_two 5 == 4
#guard Eth20Dafny.largestIndexOfOne [false, false, true, false, false, false, false, false] == 2
#guard 0 < (Eth20Dafny.fromBitlistToBytes [true, false]).length
#guard Eth20Dafny.fromBytesToBitList (Eth20Dafny.fromBitlistToBytes [true, false]) == [true, false]
#guard Eth20Dafny.fromBitvectorToBytes [true, false, true] == [UInt8.ofNat 5]
#guard Eth20Dafny.fromBytesToBitVector [UInt8.ofNat 5] 3 == [true, false, true]
#guard Eth20Dafny.boolToBytes true == [UInt8.ofNat 1]
#guard Eth20Dafny.boolSeDesByteToBool [UInt8.ofNat 0] == false
#guard Eth20Dafny.fromBitsToBytes [true, false, true, false, false, false, false, false, true] == [UInt8.ofNat 5, UInt8.ofNat 1]
#guard Eth20Dafny.sizeOf (Eth20Dafny.RawSerialisable.Uint16 7) == 2
#guard
  match Eth20Dafny.default Eth20Dafny.Tipe.Bool_ with
  | Eth20Dafny.RawSerialisable.Bool false => true
  | _ => false
#guard Eth20Dafny.serialise (Eth20Dafny.RawSerialisable.Bool true) == [UInt8.ofNat 1]
#guard Eth20Dafny.serialiseSeqOfBasics
    [Eth20Dafny.RawSerialisable.Bool true, Eth20Dafny.RawSerialisable.Bool false]
  == [UInt8.ofNat 1, UInt8.ofNat 0]
#guard
  match Eth20Dafny.deserialise [UInt8.ofNat 1] Eth20Dafny.Tipe.Bool_ with
  | Eth20Dafny.Try.Success (Eth20Dafny.RawSerialisable.Bool true) => true
  | _ => false
