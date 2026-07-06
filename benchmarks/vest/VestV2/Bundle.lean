import VestV2.Impl.Errors
import VestV2.Impl.Utils
import VestV2.Impl.RegularBytes
import VestV2.Impl.RegularEnd
import VestV2.Impl.RegularFail
import VestV2.Impl.RegularSuccess
import VestV2.Impl.RegularLeb128
import VestV2.Impl.RegularClone
import VestV2.Impl.RegularTag
import VestV2.Impl.BitcoinVarint

/-!
# VestV2.Bundle

Per-package implementation bundle for the `VestV2` root package.
Collects the scored API surface into one structure. Frozen support
modules and background theory stay outside this bundle and are not
directly replaceable by candidate implementations.

DO NOT MODIFY — benchmark infrastructure.
-/

structure VestV2Bundle where
  fromParseError     : VestV2.FromParseErrorSig
  fromSerializeError : VestV2.FromSerializeErrorSig
  setRange           : VestV2.SetRangeSig
  compareSlice       : VestV2.CompareSliceSig
  initVecU8          : VestV2.InitVecU8Sig
  variableParse      : VestV2.VariableParseSig
  variableSerialize  : VestV2.VariableSerializeSig
  fixedParse         : VestV2.FixedParseSig
  fixedSerialize     : VestV2.FixedSerializeSig
  tailParse          : VestV2.TailParseSig
  tailSerialize      : VestV2.TailSerializeSig
  endParse           : VestV2.EndParseSig
  endSerialize       : VestV2.EndSerializeSig
  failParse          : VestV2.FailParseSig
  failSerialize      : VestV2.FailSerializeSig
  successParse       : VestV2.SuccessParseSig
  successSerialize   : VestV2.SuccessSerializeSig
  leb128Parse        : VestV2.Leb128ParseSig
  cloneU8            : VestV2.CloneU8Sig
  cloneU16Le         : VestV2.CloneU16LeSig
  cloneU32Le         : VestV2.CloneU32LeSig
  cloneU64Le         : VestV2.CloneU64LeSig
  cloneTail          : VestV2.CloneTailSig
  cloneVariable      : VestV2.CloneVariableSig
  cloneFixed         : VestV2.CloneFixedSig
  tagParse           : VestV2.TagParseSig
  tagSerialize       : VestV2.TagSerializeSig
  btcVarintParse     : VestV2.BtcVarintParseSig
  btcVarintSerialize : VestV2.BtcVarintSerializeSig
