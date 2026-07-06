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

open Eth20Dafny

/-!
# Eth20Dafny.Bundle

Per-package implementation bundle for Eth20Dafny.
Collects all API signatures into one structure for harness wiring.
*-/

structure Eth20DafnyBundle where
  largestIndexOfOne : LargestIndexOfOneSig
  fromBitlistToBytes : FromBitlistToBytesSig
  fromBytesToBitList : FromBytesToBitListSig
  fromBitvectorToBytes : FromBitvectorToBytesSig
  fromBytesToBitVector : FromBytesToBitVectorSig
  boolToBytes : BoolToBytesSig
  boolSeDesByteToBool : BoolSeDesByteToBoolSig
  boolToByte : BoolToByteSig
  bytesAndBitsByteToBool : BytesAndBitsByteToBoolSig
  list8BitsToByte : List8BitsToByteSig
  byteTo8Bits : ByteTo8BitsSig
  fromBitsToBytes : FromBitsToBytesSig
  uintSe : UintSeSig
  uintDes : UintDesSig
  sizeOf : SizeOfSig
  default : DefaultSig
  serialise : SerialiseSig
  serialiseSeqOfBasics : SerialiseSeqOfBasicsSig
  deserialise : DeserialiseSig
  get_next_power_of_two : GetNextPowerOfTwoSig
  get_prev_power_of_two : GetPrevPowerOfTwoSig
