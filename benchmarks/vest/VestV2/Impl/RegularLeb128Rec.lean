import VestV2.Impl.RegularLeb128

/-!
# VestV2.Impl.RegularLeb128Rec

Recursive unsigned LEB128 parse and serialize combinators.
`UnsignedLEB128Rec` is the combinator tag type. The recursive parse
mirrors the structure of `Leb128.spec_parse`; the recursive serialize
mirrors `Leb128.spec_serialize`, splicing bytes into a buffer.

Types, signatures, and helper bodies are fixed vocabulary (DO NOT MODIFY).
-/

-- ── Types (DO NOT MODIFY) ─────────────────────────────────

/-- Tag type for the recursive LEB128 combinator. -/
structure UnsignedLEB128Rec where
  deriving Inhabited

namespace VestV2

-- ── API signatures (DO NOT MODIFY) ────────────────────────

/-- Recursively parse an unsigned LEB128-encoded integer from a byte
    slice; returns (bytes_consumed, value). -/
abbrev Leb128RecParseSig := List UInt8 → Except ParseError (Nat × Nat)

/-- Recursively serialize a natural number in unsigned LEB128 into a
    buffer at a given position; returns (bytes_written, updated_buffer). -/
abbrev Leb128RecSerializeSig := Nat → List UInt8 → Nat → Except SerializeError (Nat × List UInt8)

end VestV2


def VestV2.leb128RecParse : VestV2.Leb128RecParseSig :=
  let rec go (s : List UInt8) : Except ParseError (Nat × Nat) :=
    match s with
    | [] => Except.error ParseError.UnexpectedEndOfInput
    | b :: rest =>
      let v := takeLow7Bits b.toNat
      if isHigh8BitSet b.toNat then
        match go rest with
        | Except.ok (n, v2) =>
          if 0 < v2 ∧ v2 ≤ nBitMaxUnsigned (8 * uintSize - 7) then
            Except.ok (n + 1, (v2 <<< 7) ||| v)
          else
            Except.error (ParseError.Other "LEB128 overflow or canonicity violation")
        | Except.error e => Except.error e
      else
        Except.ok (1, v)
  fun s => go s

def leb128RecSerializeGo (v : Nat) (buf : List UInt8) (pos : Nat) :
    Except SerializeError (Nat × List UInt8) :=
  let lo := takeLow7Bits v
  let hi := v >>> 7
  if _h : hi = 0 then
    if pos ≥ buf.length then
      Except.error SerializeError.InsufficientBuffer
    else
      Except.ok (1, buf.set pos lo.toUInt8)
  else
    if pos ≥ buf.length then
      Except.error SerializeError.InsufficientBuffer
    else
      match leb128RecSerializeGo hi buf (pos + 1) with
      | Except.ok (n, buf') =>
        Except.ok (n + 1, buf'.set pos (setHigh8Bit lo).toUInt8)
      | Except.error e => Except.error e
termination_by v
decreasing_by
  have h' : v >>> 7 ≠ 0 := ‹_›
  rw [Nat.shiftRight_eq_div_pow] at h' ⊢
  have h128 : (2 : Nat) ^ 7 = 128 := by decide
  rw [h128] at h' ⊢
  have hv : 0 < v := by
    cases Nat.eq_zero_or_pos v with
    | inl h0 => simp [h0] at h'
    | inr hp => exact hp
  exact Nat.div_lt_self hv (by decide)

def VestV2.leb128RecSerialize : VestV2.Leb128RecSerializeSig :=
  fun v buf pos => leb128RecSerializeGo v buf pos
