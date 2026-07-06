import VestV2.Impl.Properties

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# VestV2.Impl.RegularLeb128

Unsigned LEB128 variable-length integer encoding/decoding.
`UnsignedLEB128` is the combinator type; `UInt` is the value type (Nat,
modeling u64). The exec `leb128Parse` decodes a byte slice into
(bytes_consumed, value).

Types, spec helpers, and signatures are fixed vocabulary (DO NOT MODIFY).
Implement only the function bodies.
-/

-- ── Types (DO NOT MODIFY) ─────────────────────────────────

/-- The unsigned LEB128 combinator (unit-like). -/
structure UnsignedLEB128 where
  deriving Inhabited

/-- Value type for LEB128: natural number modeling u64. -/
abbrev UInt := Nat

-- ── Spec helpers (no markers — fixed vocabulary) ──────────

/-- Size of UInt in bytes (models `uint_size!()` = 8). -/
def uintSize : Nat := 8

/-- Maximum value for an n-bit unsigned integer: 2^n - 1. -/
def nBitMaxUnsigned (n : Nat) : Nat :=
  if n == 0 then 0 else (1 <<< n) - 1

/-- Max u64 value: 2^64 - 1. -/
def uintMax : Nat := nBitMaxUnsigned (8 * uintSize)

/-- Check if a value fits in u64. -/
def leb128Fits (v : UInt) : Bool := v ≤ uintMax

/-- Take the lowest 7 bits of a byte. -/
def takeLow7Bits (v : Nat) : Nat := v &&& 0x7f

/-- Check if the highest bit of a byte is set (≥ 0x80). -/
def isHigh8BitSet (v : Nat) : Bool := v ≥ 0x80

/-- Set the highest bit to 1 (OR with 0x80). -/
def setHigh8Bit (v : Nat) : Nat := v ||| 0x80

namespace Leb128

/-- Specification of LEB128 parse (recursive).
    Returns `some (bytes_consumed, value)` or `none`. -/
def spec_parse : List UInt8 → Option (Int × UInt)
  | [] => none
  | b :: rest =>
    let v := takeLow7Bits b.toNat
    if isHigh8BitSet b.toNat then
      match spec_parse rest with
      | some (n, v2) =>
        -- overflow / canonicity check: v2 must be positive and fit
        if n < USize.size ∧ 0 < v2 ∧ v2 ≤ nBitMaxUnsigned (8 * uintSize - 7) then
          some (n + 1, (v2 <<< 7) ||| v)
        else
          none
      | none => none
    else
      some (1, v)

/-- Specification of LEB128 serialize (recursive). -/
def spec_serialize (v : UInt) : List UInt8 :=
  let lo := takeLow7Bits v
  let hi := v >>> 7
  if _h : hi = 0 then
    [lo.toUInt8]
  else
    (setHigh8Bit lo).toUInt8 :: spec_serialize hi
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

end Leb128

namespace VestV2

-- ── API signatures (DO NOT MODIFY) ────────────────────────

/-- Parse an unsigned LEB128-encoded integer from a byte slice;
    returns (bytes_consumed, value) where value fits in u64. -/
abbrev Leb128ParseSig := List UInt8 → Except ParseError (Nat × Nat)

end VestV2

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- !benchmark @start code_aux def=leb128Parse
-- !benchmark @end code_aux def=leb128Parse

def VestV2.leb128Parse : VestV2.Leb128ParseSig :=
-- !benchmark @start code def=leb128Parse
  fun s =>
    let rec loop (bytes : List UInt8) (acc : Nat) (shift : Nat) (i : Nat) : Except ParseError (Nat × Nat) :=
      match bytes with
      | [] => Except.error ParseError.UnexpectedEndOfInput
      | b :: rest =>
        let v := takeLow7Bits b.toNat
        let hiSet := isHigh8BitSet b.toNat
        -- Overflow check at byte 9 (0-indexed)
        if i == 9 && (hiSet || v > 1) then
          Except.error (ParseError.Other "LEB128 overflow")
        else
          let acc' := acc ||| (v <<< shift)
          if !hiSet then
            -- Canonicity: last byte of multi-byte encoding must not be 0
            if i != 0 && v == 0 then
              Except.error (ParseError.Other "failing LEB128 canonicity")
            else
              Except.ok (i + 1, acc')
          else
            loop rest acc' (shift + 7) (i + 1)
    loop s 0 0 0
-- !benchmark @end code def=leb128Parse
