import VerifiedBitmasks.Impl.BitFields

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# VerifiedBitmasks.Impl.MachineWords

Machine-word bitwise operations over 64-bit unsigned integers (`UInt64`).
Each API wraps the corresponding `BitVec 64` operation via `WordToBits`/`BitsToWord`
round-trips, faithfully translating the Dafny `MachineWords` module.

Translated from `src/BitFields/MachineWords.i.dfy`.

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
Implement only the function bodies.
-/

-- ── Spec helpers (frozen vocabulary, no markers) ──────────────────────────────

namespace MachineWords
/-- Predicate: bit index `i` is in the half-open range `[0, n)`. -/
def InRange (i n : UInt64) : Prop := i < n
end MachineWords

/-- Convert a `UInt64` machine word to a 64-element boolean list (LSB first). -/
def BitwiseToSeqBool (a : UInt64) : List Bool := BitsToSeqBool (WordToBits a)

/-- Convert a 64-element boolean list (LSB first) back to a `UInt64`. -/
def SeqBoolToBitwise (s : List Bool) : UInt64 := BitsToWord (SeqBoolToBits s)

/-- Round-trip: List Bool → UInt64 → List Bool yields the original list. -/
axiom lemma_SeqToBitsToSeq (b : List Bool) (h : b.length = 64) :
    BitwiseToSeqBool (SeqBoolToBitwise b) = b

/-- Round-trip: UInt64 → List Bool → UInt64 yields the original value. -/
axiom lemma_BitsToSeqToBits (b : UInt64) :
    SeqBoolToBitwise (BitwiseToSeqBool b) = b

/-- If all 64 bits agree, then the two UInt64 values are equal. -/
axiom lemma_BitwiseAllBitsEqualBVEq (a b : UInt64)
    (h : ∀ j : UInt64, j < BitFields.WORD_SIZE →
      (BitIsSet (WordToBits a) j = BitIsSet (WordToBits b) j)) : a = b

/-- Two UInt64 values are equal iff all their bit positions agree. -/
axiom lemma_BitwiseEq (a b : UInt64) :
    (a = b) ↔ (∀ i : UInt64, i < BitFields.WORD_SIZE →
      (BitIsSet (WordToBits a) i = BitIsSet (WordToBits b) i))

-- ── API signatures (no markers — fixed vocabulary) ────────────────────────────

namespace VerifiedBitmasks

/-- Signature: `UInt64` with only bit `i` set (`1 << i`). -/
abbrev BitwiseBitSig := UInt64 → UInt64

/-- Signature: `UInt64` constant with all 64 bits set. -/
abbrev BitwiseOnesSig := UInt64

/-- Signature: `UInt64` constant with all 64 bits cleared. -/
abbrev BitwiseZerosSig := UInt64

/-- Signature: `UInt64` mask with the low `i` bits set. -/
abbrev BitwiseMaskSig := UInt64 → UInt64

/-- Signature: Return `true` if bit `i` of `a` is set. -/
abbrev BitwiseGetBitSig := UInt64 → UInt64 → Bool

/-- Signature: Set bit `i` of `a` (force bit `i` to 1). -/
abbrev BitwiseSetBitSig := UInt64 → UInt64 → UInt64

/-- Signature: Clear bit `i` of `a` (force bit `i` to 0). -/
abbrev BitwiseClearBitSig := UInt64 → UInt64 → UInt64

/-- Signature: Toggle bit `i` of `a` (flip bit `i`). -/
abbrev BitwiseToggleBitSig := UInt64 → UInt64 → UInt64

/-- Signature: Bitwise AND of two `UInt64` values. -/
abbrev BitwiseAndSig := UInt64 → UInt64 → UInt64

/-- Signature: Bitwise OR of two `UInt64` values. -/
abbrev BitwiseOrSig := UInt64 → UInt64 → UInt64

/-- Signature: Bitwise XOR of two `UInt64` values. -/
abbrev BitwiseXorSig := UInt64 → UInt64 → UInt64

/-- Signature: Bitwise NOT (complement) of a `UInt64` value. -/
abbrev BitwiseNotSig := UInt64 → UInt64

/-- Signature: Bitwise complement via XOR with all-ones. -/
abbrev BitwiseCompSig := UInt64 → UInt64

/-- Signature: Left-shift `a` by `i` bits. -/
abbrev BitwiseLeftShiftSig := UInt64 → UInt64 → UInt64

/-- Signature: Logical right-shift `a` by `i` bits. -/
abbrev BitwiseRightShiftSig := UInt64 → UInt64 → UInt64

/-- Signature: Wrapping `UInt64` addition (mod 2^64). -/
abbrev BitwiseAddSig := UInt64 → UInt64 → UInt64

/-- Signature: Wrapping `UInt64` subtraction (mod 2^64). -/
abbrev BitwiseSubSig := UInt64 → UInt64 → UInt64

/-- Signature: Wrapping `UInt64` multiplication (mod 2^64). -/
abbrev BitwiseMulSig := UInt64 → UInt64 → UInt64

/-- Signature: Unsigned `UInt64` division (0 if divisor is 0). -/
abbrev BitwiseDivSig := UInt64 → UInt64 → UInt64

/-- Signature: Unsigned `UInt64` modulo (0 if divisor is 0). -/
abbrev BitwiseModSig := UInt64 → UInt64 → UInt64

end VerifiedBitmasks

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- ── API implementations (LLM task — fill the `code` markers) ─────────────────

-- !benchmark @start code_aux def=bitwiseBit
-- !benchmark @end code_aux def=bitwiseBit

def VerifiedBitmasks.bitwiseBit : VerifiedBitmasks.BitwiseBitSig :=
-- !benchmark @start code def=bitwiseBit
  fun i => BitsToWord (Bit i)
-- !benchmark @end code def=bitwiseBit

-- !benchmark @start code_aux def=bitwiseOnes
-- !benchmark @end code_aux def=bitwiseOnes

def VerifiedBitmasks.bitwiseOnes : VerifiedBitmasks.BitwiseOnesSig :=
-- !benchmark @start code def=bitwiseOnes
  0xffff_ffff_ffff_ffff
-- !benchmark @end code def=bitwiseOnes

-- !benchmark @start code_aux def=bitwiseZeros
-- !benchmark @end code_aux def=bitwiseZeros

def VerifiedBitmasks.bitwiseZeros : VerifiedBitmasks.BitwiseZerosSig :=
-- !benchmark @start code def=bitwiseZeros
  0
-- !benchmark @end code def=bitwiseZeros

-- !benchmark @start code_aux def=bitwiseMask
-- !benchmark @end code_aux def=bitwiseMask

def VerifiedBitmasks.bitwiseMask : VerifiedBitmasks.BitwiseMaskSig :=
-- !benchmark @start code def=bitwiseMask
  fun i => BitsToWord (BitMask i)
-- !benchmark @end code def=bitwiseMask

-- !benchmark @start code_aux def=bitwiseGetBit
-- !benchmark @end code_aux def=bitwiseGetBit

def VerifiedBitmasks.bitwiseGetBit : VerifiedBitmasks.BitwiseGetBitSig :=
-- !benchmark @start code def=bitwiseGetBit
  fun a i => BitIsSet (WordToBits a) i
-- !benchmark @end code def=bitwiseGetBit

-- !benchmark @start code_aux def=bitwiseSetBit
-- !benchmark @end code_aux def=bitwiseSetBit

def VerifiedBitmasks.bitwiseSetBit : VerifiedBitmasks.BitwiseSetBitSig :=
-- !benchmark @start code def=bitwiseSetBit
  fun a i => BitsToWord (BitSetBit (WordToBits a) i)
-- !benchmark @end code def=bitwiseSetBit

-- !benchmark @start code_aux def=bitwiseClearBit
-- !benchmark @end code_aux def=bitwiseClearBit

def VerifiedBitmasks.bitwiseClearBit : VerifiedBitmasks.BitwiseClearBitSig :=
-- !benchmark @start code def=bitwiseClearBit
  fun a i => BitsToWord (BitClearBit (WordToBits a) i)
-- !benchmark @end code def=bitwiseClearBit

-- !benchmark @start code_aux def=bitwiseToggleBit
-- !benchmark @end code_aux def=bitwiseToggleBit

def VerifiedBitmasks.bitwiseToggleBit : VerifiedBitmasks.BitwiseToggleBitSig :=
-- !benchmark @start code def=bitwiseToggleBit
  fun a i => BitsToWord (BitToggleBit (WordToBits a) i)
-- !benchmark @end code def=bitwiseToggleBit

-- !benchmark @start code_aux def=bitwiseAnd
-- !benchmark @end code_aux def=bitwiseAnd

def VerifiedBitmasks.bitwiseAnd : VerifiedBitmasks.BitwiseAndSig :=
-- !benchmark @start code def=bitwiseAnd
  fun a b => BitsToWord (BitAnd (WordToBits a) (WordToBits b))
-- !benchmark @end code def=bitwiseAnd

-- !benchmark @start code_aux def=bitwiseOr
-- !benchmark @end code_aux def=bitwiseOr

def VerifiedBitmasks.bitwiseOr : VerifiedBitmasks.BitwiseOrSig :=
-- !benchmark @start code def=bitwiseOr
  fun a b => BitsToWord (BitOr (WordToBits a) (WordToBits b))
-- !benchmark @end code def=bitwiseOr

-- !benchmark @start code_aux def=bitwiseXor
-- !benchmark @end code_aux def=bitwiseXor

def VerifiedBitmasks.bitwiseXor : VerifiedBitmasks.BitwiseXorSig :=
-- !benchmark @start code def=bitwiseXor
  fun a b => BitsToWord (BitXor (WordToBits a) (WordToBits b))
-- !benchmark @end code def=bitwiseXor

-- !benchmark @start code_aux def=bitwiseNot
-- !benchmark @end code_aux def=bitwiseNot

def VerifiedBitmasks.bitwiseNot : VerifiedBitmasks.BitwiseNotSig :=
-- !benchmark @start code def=bitwiseNot
  fun a => BitsToWord (BitNot (WordToBits a))
-- !benchmark @end code def=bitwiseNot

-- !benchmark @start code_aux def=bitwiseComp
-- !benchmark @end code_aux def=bitwiseComp

def VerifiedBitmasks.bitwiseComp : VerifiedBitmasks.BitwiseCompSig :=
-- !benchmark @start code def=bitwiseComp
  fun a => BitsToWord (BitComp (WordToBits a))
-- !benchmark @end code def=bitwiseComp

-- !benchmark @start code_aux def=bitwiseLeftShift
-- !benchmark @end code_aux def=bitwiseLeftShift

def VerifiedBitmasks.bitwiseLeftShift : VerifiedBitmasks.BitwiseLeftShiftSig :=
-- !benchmark @start code def=bitwiseLeftShift
  fun a i => BitsToWord (BitLeftShift (WordToBits a) i)
-- !benchmark @end code def=bitwiseLeftShift

-- !benchmark @start code_aux def=bitwiseRightShift
-- !benchmark @end code_aux def=bitwiseRightShift

def VerifiedBitmasks.bitwiseRightShift : VerifiedBitmasks.BitwiseRightShiftSig :=
-- !benchmark @start code def=bitwiseRightShift
  fun a i => BitsToWord (BitRightShift (WordToBits a) i)
-- !benchmark @end code def=bitwiseRightShift

-- !benchmark @start code_aux def=bitwiseAdd
-- !benchmark @end code_aux def=bitwiseAdd

def VerifiedBitmasks.bitwiseAdd : VerifiedBitmasks.BitwiseAddSig :=
-- !benchmark @start code def=bitwiseAdd
  fun a b => a + b
-- !benchmark @end code def=bitwiseAdd

-- !benchmark @start code_aux def=bitwiseSub
-- !benchmark @end code_aux def=bitwiseSub

def VerifiedBitmasks.bitwiseSub : VerifiedBitmasks.BitwiseSubSig :=
-- !benchmark @start code def=bitwiseSub
  fun a b => a - b
-- !benchmark @end code def=bitwiseSub

-- !benchmark @start code_aux def=bitwiseMul
-- !benchmark @end code_aux def=bitwiseMul

def VerifiedBitmasks.bitwiseMul : VerifiedBitmasks.BitwiseMulSig :=
-- !benchmark @start code def=bitwiseMul
  fun a b => a * b
-- !benchmark @end code def=bitwiseMul

-- !benchmark @start code_aux def=bitwiseDiv
-- !benchmark @end code_aux def=bitwiseDiv

def VerifiedBitmasks.bitwiseDiv : VerifiedBitmasks.BitwiseDivSig :=
-- !benchmark @start code def=bitwiseDiv
  fun a b => a / b
-- !benchmark @end code def=bitwiseDiv

-- !benchmark @start code_aux def=bitwiseMod
-- !benchmark @end code_aux def=bitwiseMod

def VerifiedBitmasks.bitwiseMod : VerifiedBitmasks.BitwiseModSig :=
-- !benchmark @start code def=bitwiseMod
  fun a b => a % b
-- !benchmark @end code def=bitwiseMod
