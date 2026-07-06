import Flocq.Core.Impl.Zaux
import Flocq.Core.Impl.Defs
import Flocq.Core.Impl.Digits
import Flocq.Core.Impl.FLX
import Flocq.Core.Impl.FLT
import Flocq.Core.Impl.RoundPred
import Flocq.Core.Impl.Ulp
import Flocq.Calc.Impl.Bracket
import Flocq.Calc.Impl.Operations
import Flocq.Calc.Impl.Div
import Flocq.Calc.Impl.Plus
import Flocq.Calc.Impl.Round
import Flocq.Calc.Impl.Sqrt
import Flocq.IEEE754.Impl.BinaryDefs
import Flocq.IEEE754.Impl.Binary
import Flocq.IEEE754.Impl.Bits
import Flocq.IEEE754.Impl.PrimFloat
import Flocq.Pff.Impl.Pff

open Flocq

/-!
# Flocq.Bundle

Per-package implementation bundle for the `Flocq` root package.
Collects all API signatures into one structure.

In `Harness.lean`, `structure RepoImpl` has a single field `flocq : FlocqBundle`.
Specs access API functions via `impl.flocq.<fn>`.

DO NOT MODIFY — benchmark infrastructure.
-/

structure FlocqBundle where
  -- Core.Zaux: integer arithmetic helpers
  zfastPowPos      : ZfastPowPosSig
  zposDivEuclAux1  : ZposDivEuclAux1Sig
  zposDivEuclAux   : ZposDivEuclAuxSig
  zfastDivEucl     : ZfastDivEuclSig
  iterNat           : IterNatSig
  -- Core.Raux: real comparison, integer projection, and base-power helpers
  rcompare          : RcompareSig
  rleBool           : RleBoolSig
  rltBool           : RltBoolSig
  reqBool           : ReqBoolSig
  ztrunc            : ZtruncSig
  zaway             : ZawaySig
  bpow              : Radix → Int → ℝ
  condRopp          : CondRoppSig
  -- Core.GenericFmt: generic rounding function (shared axiom from Core.FLT chain)
  znearest          : ZnearestSig
  round             : Radix → (Int → Int) → (ℝ → Int) → ℝ → ℝ
  -- Core.FLT: unit in the last place
  ulp               : UlpSig
  -- Core.Ulp: successor and predecessor
  succ              : SuccSig
  pred              : PredSig
  -- Core.Digits: digit count
  digits2Pnat       : Digits2PnatSig
  zsumDigit         : ZsumDigitSig
  zscale            : ZscaleSig
  zslice            : ZsliceSig
  zdigitsAux        : ZdigitsAuxSig
  zdigits           : ZdigitsSig
  -- Calc.Bracket: location tracking for rounding error
  newLocationEven   : NewLocationEvenSig
  newLocationOdd    : NewLocationOddSig
  newLocation       : NewLocationSig
  -- Calc.Operations: exact floating-point operations
  falign            : FalignSig
  fopp              : FoppSig
  fabs              : FabsSig
  fmult             : FmultSig
  -- Calc.Div: integer division kernel
  fdivCore          : FdivCoreSig
  fdiv              : FdivSig
  -- Calc.Plus: integer addition kernel
  fplusCore         : FplusCoreSig
  fplus             : FplusSig
  -- Calc.Round: mantissa truncation / rounding
  condIncr          : CondIncrSig
  roundSignDN       : RoundSignDNSig
  roundUP           : RoundUPSig
  roundSignUP       : RoundSignUPSig
  roundZR           : RoundZRSig
  roundN            : RoundNSig
  truncateAux       : TruncateAuxSig
  truncate          : TruncateSig
  truncateFIX       : TruncateFIXSig
  -- Calc.Sqrt: integer square-root kernel
  fsqrtCore         : FsqrtCoreSig
  fsqrt             : FsqrtSig
  -- IEEE754.Binary: core IEEE 754 binary float operations
  b2R               : B2RSig
  isFinite          : IsFiniteSig
  isNaN             : IsNaNSig
  roundMode         : RoundModeSig
  b2FF              : B2FFSig
  ff2B              : FF2BSig
  binaryNormalize   : BinaryNormalizeSig
  babs              : BabsSig
  bcompare          : BcompareSig
  bdiv              : BdivSig
  bfma              : BfmaSig
  bfrexp            : BfrexpSig
  bldexp            : BldexpSig
  bmaxFloat         : BmaxFloatSig
  bminus            : BminusSig
  bmult             : BmultSig
  bnearbyint        : BnearbyintSig
  bone              : BoneSig
  bopp              : BoppSig
  bplus             : BplusSig
  bpred             : BpredSig
  bsqrt             : BsqrtSig
  bsucc             : BsuccSig
  btrunc            : BtruncSig
  bulp              : BulpSig
  -- IEEE754.Bits: bit-pattern encoding/decoding and b32/b64 operations
  validBinary       : ValidBinarySig
  binopNanPl32      : BinopNanPl32Sig
  binopNanPl64      : BinopNanPl64Sig
  unopNanPl32       : UnopNanPl32Sig
  unopNanPl64       : UnopNanPl64Sig
  ternopNanPl32     : TernopNanPl32Sig
  ternopNanPl64     : TernopNanPl64Sig
  splitBits         : SplitBitsSig
  splitBitsOfBinaryFloat : SplitBitsOfBinaryFloatSig
  binaryFloatOfBitsAux : BinaryFloatOfBitsAuxSig
  bitsOfBinaryFloat : BitsOfBinaryFloatSig
  binaryFloatOfBits : BinaryFloatOfBitsSig
  b32OfBits         : B32OfBitsSig
  b64OfBits         : B64OfBitsSig
  bitsOfB32         : BitsOfB32Sig
  bitsOfB64         : BitsOfB64Sig
  b32Plus           : B32PlusSig
  b32Minus          : B32MinusSig
  b32Mult           : B32MultSig
  b32Div            : B32DivSig
  b32Sqrt           : B32SqrtSig
  b32Fma            : B32FmaSig
  b64Plus           : B64PlusSig
  b64Minus          : B64MinusSig
  b64Mult           : B64MultSig
  b64Div            : B64DivSig
  b64Sqrt           : B64SqrtSig
  b64Fma            : B64FmaSig
  -- IEEE754.PrimFloat: native Float ↔ BinaryFloat conversion
  b2Prim            : B2PrimSig
  prim2B            : Prim2BSig
  -- Pff.Pff: source-backed Pff float operations and finite list helpers
  pffFopp           : PffFoppSig
  pffFabs           : PffFabsSig
  pffFplus          : PffFplusSig
  pffFmult          : PffFmultSig
  pffMZlistAux      : PffMZlistAuxSig
  pffMZlist         : PffMZlistSig
  pffMProd          : PffMProdSig
