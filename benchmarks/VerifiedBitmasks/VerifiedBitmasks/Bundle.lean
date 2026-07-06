import VerifiedBitmasks.Impl.MachineWords
import VerifiedBitmasks.Impl.BitmaskIF
import VerifiedBitmasks.Impl.BitmaskImplIF
import VerifiedBitmasks.Impl.BitmaskFixedChunks
import VerifiedBitmasks.Impl.BitmaskSeq
import VerifiedBitmasks.Impl.BitmaskArray

/-!
# VerifiedBitmasks.Bundle

Per-package implementation bundle for the `VerifiedBitmasks` root package.
Collects all 88 API function signatures into one structure.

In `Harness.lean`, `RepoImpl` holds one field `verifiedBitmasks :
VerifiedBitmasksBundle`. Specs access API functions via
`impl.verifiedBitmasks.<fn>`.

DO NOT MODIFY — benchmark infrastructure.
-/

structure VerifiedBitmasksBundle where
  -- ── MachineWords (20 APIs) ──────────────────────────────────────────
  bitwiseBit         : VerifiedBitmasks.BitwiseBitSig
  bitwiseOnes        : VerifiedBitmasks.BitwiseOnesSig
  bitwiseZeros       : VerifiedBitmasks.BitwiseZerosSig
  bitwiseMask        : VerifiedBitmasks.BitwiseMaskSig
  bitwiseGetBit      : VerifiedBitmasks.BitwiseGetBitSig
  bitwiseSetBit      : VerifiedBitmasks.BitwiseSetBitSig
  bitwiseClearBit    : VerifiedBitmasks.BitwiseClearBitSig
  bitwiseToggleBit   : VerifiedBitmasks.BitwiseToggleBitSig
  bitwiseAnd         : VerifiedBitmasks.BitwiseAndSig
  bitwiseOr          : VerifiedBitmasks.BitwiseOrSig
  bitwiseXor         : VerifiedBitmasks.BitwiseXorSig
  bitwiseNot         : VerifiedBitmasks.BitwiseNotSig
  bitwiseComp        : VerifiedBitmasks.BitwiseCompSig
  bitwiseLeftShift   : VerifiedBitmasks.BitwiseLeftShiftSig
  bitwiseRightShift  : VerifiedBitmasks.BitwiseRightShiftSig
  bitwiseAdd         : VerifiedBitmasks.BitwiseAddSig
  bitwiseSub         : VerifiedBitmasks.BitwiseSubSig
  bitwiseMul         : VerifiedBitmasks.BitwiseMulSig
  bitwiseDiv         : VerifiedBitmasks.BitwiseDivSig
  bitwiseMod         : VerifiedBitmasks.BitwiseModSig
  -- ── BitmaskIF (14 APIs) ─────────────────────────────────────────────
  bIF_newZeros       : VerifiedBitmasks.BIFNewZerosSig
  bIF_newOnes        : VerifiedBitmasks.BIFNewOnesSig
  bIF_concat         : VerifiedBitmasks.BIFConcatSig
  bIF_split          : VerifiedBitmasks.BIFSplitSig
  bIF_nbits          : VerifiedBitmasks.BIFNbitsSig
  bIF_popcnt         : VerifiedBitmasks.BIFPopcntSig
  bIF_getBit         : VerifiedBitmasks.BIFGetBitSig
  bIF_setBit         : VerifiedBitmasks.BIFSetBitSig
  bIF_clearBit       : VerifiedBitmasks.BIFClearBitSig
  bIF_toggleBit      : VerifiedBitmasks.BIFToggleBitSig
  bIF_and            : VerifiedBitmasks.BIFAndSig
  bIF_or             : VerifiedBitmasks.BIFOrSig
  bIF_xor            : VerifiedBitmasks.BIFXorSig
  bIF_not            : VerifiedBitmasks.BIFNotSig
  -- ── BitmaskImplIF (12 APIs) ─────────────────────────────────────────
  bIIF_newZeros      : VerifiedBitmasks.BIIFNewZerosSig
  bIIF_newOnes       : VerifiedBitmasks.BIIFNewOnesSig
  bIIF_nbits         : VerifiedBitmasks.BIIFNbitsSig
  bIIF_popcnt        : VerifiedBitmasks.BIIFPopcntSig
  bIIF_getBit        : VerifiedBitmasks.BIIFGetBitSig
  bIIF_setBit        : VerifiedBitmasks.BIIFSetBitSig
  bIIF_clearBit      : VerifiedBitmasks.BIIFClearBitSig
  bIIF_toggleBit     : VerifiedBitmasks.BIIFToggleBitSig
  bIIF_and           : VerifiedBitmasks.BIIFAndSig
  bIIF_or            : VerifiedBitmasks.BIIFOrSig
  bIIF_xor           : VerifiedBitmasks.BIIFXorSig
  bIIF_not           : VerifiedBitmasks.BIIFNotSig
  -- ── BitmaskFixedChunks (12 APIs) ────────────────────────────────────
  bFC_newZeros       : VerifiedBitmasks.BFCNewZerosSig
  bFC_newOnes        : VerifiedBitmasks.BFCNewOnesSig
  bFC_nbits          : VerifiedBitmasks.BFCNbitsSig
  bFC_popcnt         : VerifiedBitmasks.BFCPopcntSig
  bFC_getBit         : VerifiedBitmasks.BFCGetBitSig
  bFC_setBit         : VerifiedBitmasks.BFCSetBitSig
  bFC_clearBit       : VerifiedBitmasks.BFCClearBitSig
  bFC_toggleBit      : VerifiedBitmasks.BFCToggleBitSig
  bFC_and            : VerifiedBitmasks.BFCAndSig
  bFC_or             : VerifiedBitmasks.BFCOrSig
  bFC_xor            : VerifiedBitmasks.BFCXorSig
  bFC_not            : VerifiedBitmasks.BFCNotSig
  -- ── BitmaskSeq (15 APIs) ────────────────────────────────────────────
  bSeq_cNewZeros     : VerifiedBitmasks.BSeqCNewZerosSig
  bSeq_cNewOnes      : VerifiedBitmasks.BSeqCNewOnesSig
  bSeq_nbits         : VerifiedBitmasks.BSeqNbitsSig
  bSeq_popcnt        : VerifiedBitmasks.BSeqPopcntSig
  bSeq_getBit        : VerifiedBitmasks.BSeqGetBitSig
  bSeq_setBit        : VerifiedBitmasks.BSeqSetBitSig
  bSeq_clearBit      : VerifiedBitmasks.BSeqClearBitSig
  bSeq_toggleBit     : VerifiedBitmasks.BSeqToggleBitSig
  bSeq_eq            : VerifiedBitmasks.BSeqEqSig
  bSeq_isZeros       : VerifiedBitmasks.BSeqIsZerosSig
  bSeq_isOnes        : VerifiedBitmasks.BSeqIsOnesSig
  bSeq_and           : VerifiedBitmasks.BSeqAndSig
  bSeq_or            : VerifiedBitmasks.BSeqOrSig
  bSeq_xor           : VerifiedBitmasks.BSeqXorSig
  bSeq_not           : VerifiedBitmasks.BSeqNotSig
  -- ── BitmaskArray (15 APIs) ──────────────────────────────────────────
  bArr_cNewZeros     : VerifiedBitmasks.BArrCNewZerosSig
  bArr_cNewOnes      : VerifiedBitmasks.BArrCNewOnesSig
  bArr_nbits         : VerifiedBitmasks.BArrNbitsSig
  bArr_popcnt        : VerifiedBitmasks.BArrPopcntSig
  bArr_getBit        : VerifiedBitmasks.BArrGetBitSig
  bArr_setBit        : VerifiedBitmasks.BArrSetBitSig
  bArr_clearBit      : VerifiedBitmasks.BArrClearBitSig
  bArr_toggleBit     : VerifiedBitmasks.BArrToggleBitSig
  bArr_eq            : VerifiedBitmasks.BArrEqSig
  bArr_isZeros       : VerifiedBitmasks.BArrIsZerosSig
  bArr_isOnes        : VerifiedBitmasks.BArrIsOnesSig
  bArr_and           : VerifiedBitmasks.BArrAndSig
  bArr_or            : VerifiedBitmasks.BArrOrSig
  bArr_xor           : VerifiedBitmasks.BArrXorSig
  bArr_not           : VerifiedBitmasks.BArrNotSig
