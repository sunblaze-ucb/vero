import VerifiedBitmasks.BitFields.BitFields

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# VerifiedBitmasks.BitFields.MachineWords

Machine-word-level bitwise operations over `UInt64`.

Each function wraps the underlying `BitVec 64` operations from
`BitFields` via the `BitsToWord` / `WordToBits` round-trip.

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
Implement only the function bodies (inside the `!benchmark code` markers).
-/

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- ── Spec helpers (fully defined, no markers, curator-given) ────────────────

/-- Convert a `UInt64` machine word to a 64-element boolean list (LSB first). -/
def BitwiseToSeqBool (a : UInt64) : List Bool := BitsToSeqBool (WordToBits a)

/-- Convert a 64-element boolean list (LSB first) back to a `UInt64`. -/
def SeqBoolToBitwise (s : List Bool) : UInt64 := BitsToWord (SeqBoolToBits s)

-- ── API signatures (no markers — fixed vocabulary) ─────────────────────────

namespace Bank

abbrev BitwiseBitSig          := UInt64 → UInt64
abbrev BitwiseOnesSig         := UInt64
abbrev BitwiseZerosSig        := UInt64
abbrev BitwiseMaskSig         := UInt64 → UInt64
abbrev BitwiseGetBitSig       := UInt64 → UInt64 → Bool
abbrev BitwiseSetBitSig       := UInt64 → UInt64 → UInt64
abbrev BitwiseClearBitSig     := UInt64 → UInt64 → UInt64
abbrev BitwiseToggleBitSig    := UInt64 → UInt64 → UInt64
abbrev BitwiseAndSig          := UInt64 → UInt64 → UInt64
abbrev BitwiseOrSig           := UInt64 → UInt64 → UInt64
abbrev BitwiseXorSig          := UInt64 → UInt64 → UInt64
abbrev BitwiseNotSig          := UInt64 → UInt64
abbrev BitwiseCompSig         := UInt64 → UInt64
abbrev BitwiseLeftShiftSig    := UInt64 → UInt64 → UInt64
abbrev BitwiseRightShiftSig   := UInt64 → UInt64 → UInt64
abbrev BitwiseAddSig          := UInt64 → UInt64 → UInt64
abbrev BitwiseSubSig          := UInt64 → UInt64 → UInt64
abbrev BitwiseMulSig          := UInt64 → UInt64 → UInt64
abbrev BitwiseDivSig          := UInt64 → UInt64 → UInt64
abbrev BitwiseModSig          := UInt64 → UInt64 → UInt64

end Bank

-- ── Implementation stubs (LLM task) ────────────────────────────────────────

-- !benchmark @start code_aux def=bitwiseBit
-- !benchmark @end code_aux def=bitwiseBit

def Bank.bitwiseBit : Bank.BitwiseBitSig :=
-- !benchmark @start code def=bitwiseBit
  fun i => BitsToWord (Bit i)
-- !benchmark @end code def=bitwiseBit

-- !benchmark @start code_aux def=bitwiseOnes
-- !benchmark @end code_aux def=bitwiseOnes

def Bank.bitwiseOnes : Bank.BitwiseOnesSig :=
-- !benchmark @start code def=bitwiseOnes
  0xffff_ffff_ffff_ffff
-- !benchmark @end code def=bitwiseOnes

-- !benchmark @start code_aux def=bitwiseZeros
-- !benchmark @end code_aux def=bitwiseZeros

def Bank.bitwiseZeros : Bank.BitwiseZerosSig :=
-- !benchmark @start code def=bitwiseZeros
  0
-- !benchmark @end code def=bitwiseZeros

-- !benchmark @start code_aux def=bitwiseMask
-- !benchmark @end code_aux def=bitwiseMask

def Bank.bitwiseMask : Bank.BitwiseMaskSig :=
-- !benchmark @start code def=bitwiseMask
  fun i => BitsToWord (BitMask i)
-- !benchmark @end code def=bitwiseMask

-- !benchmark @start code_aux def=bitwiseGetBit
-- !benchmark @end code_aux def=bitwiseGetBit

def Bank.bitwiseGetBit : Bank.BitwiseGetBitSig :=
-- !benchmark @start code def=bitwiseGetBit
  fun a i => BitIsSet (WordToBits a) i
-- !benchmark @end code def=bitwiseGetBit

-- !benchmark @start code_aux def=bitwiseSetBit
-- !benchmark @end code_aux def=bitwiseSetBit

def Bank.bitwiseSetBit : Bank.BitwiseSetBitSig :=
-- !benchmark @start code def=bitwiseSetBit
  fun a i => BitsToWord (BitSetBit (WordToBits a) i)
-- !benchmark @end code def=bitwiseSetBit

-- !benchmark @start code_aux def=bitwiseClearBit
-- !benchmark @end code_aux def=bitwiseClearBit

def Bank.bitwiseClearBit : Bank.BitwiseClearBitSig :=
-- !benchmark @start code def=bitwiseClearBit
  fun a i => BitsToWord (BitClearBit (WordToBits a) i)
-- !benchmark @end code def=bitwiseClearBit

-- !benchmark @start code_aux def=bitwiseToggleBit
-- !benchmark @end code_aux def=bitwiseToggleBit

def Bank.bitwiseToggleBit : Bank.BitwiseToggleBitSig :=
-- !benchmark @start code def=bitwiseToggleBit
  fun a bit =>
    if Bank.bitwiseGetBit a bit then Bank.bitwiseClearBit a bit
    else Bank.bitwiseSetBit a bit
-- !benchmark @end code def=bitwiseToggleBit

-- !benchmark @start code_aux def=bitwiseAnd
-- !benchmark @end code_aux def=bitwiseAnd

def Bank.bitwiseAnd : Bank.BitwiseAndSig :=
-- !benchmark @start code def=bitwiseAnd
  fun a b => BitsToWord (BitAnd (WordToBits a) (WordToBits b))
-- !benchmark @end code def=bitwiseAnd

-- !benchmark @start code_aux def=bitwiseOr
-- !benchmark @end code_aux def=bitwiseOr

def Bank.bitwiseOr : Bank.BitwiseOrSig :=
-- !benchmark @start code def=bitwiseOr
  fun a b => BitsToWord (BitOr (WordToBits a) (WordToBits b))
-- !benchmark @end code def=bitwiseOr

-- !benchmark @start code_aux def=bitwiseXor
-- !benchmark @end code_aux def=bitwiseXor

def Bank.bitwiseXor : Bank.BitwiseXorSig :=
-- !benchmark @start code def=bitwiseXor
  fun a b => BitsToWord (BitXor (WordToBits a) (WordToBits b))
-- !benchmark @end code def=bitwiseXor

-- !benchmark @start code_aux def=bitwiseNot
-- !benchmark @end code_aux def=bitwiseNot

def Bank.bitwiseNot : Bank.BitwiseNotSig :=
-- !benchmark @start code def=bitwiseNot
  fun a => BitsToWord (BitNot (WordToBits a))
-- !benchmark @end code def=bitwiseNot

-- !benchmark @start code_aux def=bitwiseComp
-- !benchmark @end code_aux def=bitwiseComp

def Bank.bitwiseComp : Bank.BitwiseCompSig :=
-- !benchmark @start code def=bitwiseComp
  fun a => BitsToWord (BitComp (WordToBits a))
-- !benchmark @end code def=bitwiseComp

-- !benchmark @start code_aux def=bitwiseLeftShift
-- !benchmark @end code_aux def=bitwiseLeftShift

def Bank.bitwiseLeftShift : Bank.BitwiseLeftShiftSig :=
-- !benchmark @start code def=bitwiseLeftShift
  fun a i => BitsToWord (BitLeftShift (WordToBits a) i)
-- !benchmark @end code def=bitwiseLeftShift

-- !benchmark @start code_aux def=bitwiseRightShift
-- !benchmark @end code_aux def=bitwiseRightShift

def Bank.bitwiseRightShift : Bank.BitwiseRightShiftSig :=
-- !benchmark @start code def=bitwiseRightShift
  fun a i => BitsToWord (BitRightShift (WordToBits a) i)
-- !benchmark @end code def=bitwiseRightShift

-- !benchmark @start code_aux def=bitwiseAdd
-- !benchmark @end code_aux def=bitwiseAdd

def Bank.bitwiseAdd : Bank.BitwiseAddSig :=
-- !benchmark @start code def=bitwiseAdd
  fun a b => a + b
-- !benchmark @end code def=bitwiseAdd

-- !benchmark @start code_aux def=bitwiseSub
-- !benchmark @end code_aux def=bitwiseSub

def Bank.bitwiseSub : Bank.BitwiseSubSig :=
-- !benchmark @start code def=bitwiseSub
  fun a b => a - b
-- !benchmark @end code def=bitwiseSub

-- !benchmark @start code_aux def=bitwiseMul
-- !benchmark @end code_aux def=bitwiseMul

def Bank.bitwiseMul : Bank.BitwiseMulSig :=
-- !benchmark @start code def=bitwiseMul
  fun a b => a * b
-- !benchmark @end code def=bitwiseMul

-- !benchmark @start code_aux def=bitwiseDiv
-- !benchmark @end code_aux def=bitwiseDiv

def Bank.bitwiseDiv : Bank.BitwiseDivSig :=
-- !benchmark @start code def=bitwiseDiv
  fun a b => a / b
-- !benchmark @end code def=bitwiseDiv

-- !benchmark @start code_aux def=bitwiseMod
-- !benchmark @end code_aux def=bitwiseMod

def Bank.bitwiseMod : Bank.BitwiseModSig :=
-- !benchmark @start code def=bitwiseMod
  fun a b => a % b
-- !benchmark @end code def=bitwiseMod
