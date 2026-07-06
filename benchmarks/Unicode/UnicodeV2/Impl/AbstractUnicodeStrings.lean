import UnicodeV2.Impl.Unicode

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Unicode.Impl.AbstractUnicodeStrings

Interface for converting between Lean `String` values and sequences of
UTF-8 bytes (`List UInt8`) or UTF-16 code units (`List UInt16`).

Lean 4 `String` values are always valid sequences of Unicode scalar
values (surrogates are not valid `Char` values), so the UTF-8 and
UTF-16 encoding directions always succeed. The decoding directions may
return `none` when the input byte/code-unit sequence is malformed.

Types and signatures are fixed vocabulary (DO NOT MODIFY). Function
bodies are the curator's reference implementations; the pipeline
replaces them with `sorry` inside the `code` markers before presenting
the benchmark to the LLM.
-/

namespace Unicode

-- ── API signatures (DO NOT MODIFY) ───────────────────────────────────────────

/-- Signature: convert a string to its UTF-8 byte representation. -/
abbrev AbsToUTF8CheckedSig   := String → Option (List UInt8)

/-- Signature: convert an ASCII-only string to bytes. Source Dafny requires
    every character to be below 128; the Lean function is total but guards and
    specs use it only under that precondition. -/
abbrev AbsASCIIToUTF8Sig := String → List UInt8

/-- Signature: decode a UTF-8 byte sequence to a string. -/
abbrev AbsFromUTF8CheckedSig := List UInt8 → Option String

/-- Signature: convert a string to its UTF-16 code unit representation. -/
abbrev AbsToUTF16CheckedSig  := String → Option (List UInt16)

/-- Signature: convert an ASCII-only string to UTF-16 code units. Source Dafny
    requires every character to be below 128; the Lean function is total but
    guards and specs use it only under that precondition. -/
abbrev AbsASCIIToUTF16Sig := String → List UInt16

/-- Signature: decode a UTF-16 code unit sequence to a string. -/
abbrev AbsFromUTF16CheckedSig := List UInt16 → Option String

end Unicode

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- ── absToUTF8Checked ─────────────────────────────────────────────────────────

-- !benchmark @start code_aux def=absToUTF8Checked
-- !benchmark @end code_aux def=absToUTF8Checked

def Unicode.absToUTF8Checked : Unicode.AbsToUTF8CheckedSig :=
-- !benchmark @start code def=absToUTF8Checked
  -- Lean 4 strings are always valid Unicode scalar-value sequences,
  -- so UTF-8 encoding always succeeds.
  fun s => some (s.toUTF8.data.toList)
-- !benchmark @end code def=absToUTF8Checked

-- ── absASCIIToUTF8 ──────────────────────────────────────────────────────────

-- !benchmark @start code_aux def=absASCIIToUTF8
-- !benchmark @end code_aux def=absASCIIToUTF8

def Unicode.absASCIIToUTF8 : Unicode.AbsASCIIToUTF8Sig :=
-- !benchmark @start code def=absASCIIToUTF8
  -- Dafny's source precondition restricts `s` to ASCII characters, where
  -- UTF-8 bytes are exactly the character code points.
  fun s => s.toList.map (fun c => c.val.toNat.toUInt8)
-- !benchmark @end code def=absASCIIToUTF8

-- ── absFromUTF8Checked ───────────────────────────────────────────────────────

-- !benchmark @start code_aux def=absFromUTF8Checked
-- !benchmark @end code_aux def=absFromUTF8Checked

def Unicode.absFromUTF8Checked : Unicode.AbsFromUTF8CheckedSig :=
-- !benchmark @start code def=absFromUTF8Checked
  -- Build a ByteArray from the byte list and attempt UTF-8 decoding.
  -- Returns none if the byte sequence is not valid UTF-8.
  fun bs => String.fromUTF8? ⟨bs.toArray⟩
-- !benchmark @end code def=absFromUTF8Checked

-- ── absToUTF16Checked ────────────────────────────────────────────────────────

-- !benchmark @start code_aux def=absToUTF16Checked
-- !benchmark @end code_aux def=absToUTF16Checked

def Unicode.absToUTF16Checked : Unicode.AbsToUTF16CheckedSig :=
-- !benchmark @start code def=absToUTF16Checked
  -- Encode each Unicode scalar value as one or two UTF-16 code units.
  -- BMP characters (< U+10000) map to a single code unit.
  -- Supplementary characters map to a surrogate pair.
  -- Lean 4 chars are always scalar values so encoding always succeeds.
  fun s =>
    some ((s.toList.map fun c =>
      let cp := c.val.toNat
      if cp < 0x10000 then
        [cp.toUInt16]
      else
        let cp' := cp - 0x10000
        [(0xD800 + cp' / 0x400).toUInt16,
         (0xDC00 + cp' % 0x400).toUInt16]).flatten)
-- !benchmark @end code def=absToUTF16Checked

-- ── absASCIIToUTF16 ─────────────────────────────────────────────────────────

-- !benchmark @start code_aux def=absASCIIToUTF16
-- !benchmark @end code_aux def=absASCIIToUTF16

def Unicode.absASCIIToUTF16 : Unicode.AbsASCIIToUTF16Sig :=
-- !benchmark @start code def=absASCIIToUTF16
  -- Dafny's source precondition restricts `s` to ASCII characters, where
  -- UTF-16 code units are exactly the character code points.
  fun s => s.toList.map (fun c => c.val.toNat.toUInt16)
-- !benchmark @end code def=absASCIIToUTF16

-- ── absFromUTF16Checked ──────────────────────────────────────────────────────

-- !benchmark @start code_aux def=absFromUTF16Checked
-- Try to build a Char from a Unicode code-point value (Nat).
-- Returns none for surrogate code points or values above U+10FFFF.
private def absFromUTF16Checked_charOfNat? (n : Nat) : Option Char :=
  let v := n.toUInt32
  if hv : v.isValidChar then some ⟨v, hv⟩ else none

-- Decode a list of UTF-16 code units into a list of Chars, returning
-- none if the sequence contains an unpaired or misplaced surrogate.
private def absFromUTF16Checked_decode : List UInt16 → Option (List Char)
  | [] => some []
  | w :: rest =>
    let v := w.toNat
    if v < 0xD800 || v > 0xDFFF then
      -- Non-surrogate BMP character.
      (absFromUTF16Checked_charOfNat? v).bind
        fun c => (absFromUTF16Checked_decode rest).map (c :: ·)
    else if v ≤ 0xDBFF then
      -- High surrogate: must be followed by a low surrogate.
      match rest with
      | w2 :: rest2 =>
        let v2 := w2.toNat
        if v2 ≥ 0xDC00 && v2 ≤ 0xDFFF then
          let cp := 0x10000 + (v - 0xD800) * 0x400 + (v2 - 0xDC00)
          (absFromUTF16Checked_charOfNat? cp).bind
            fun c => (absFromUTF16Checked_decode rest2).map (c :: ·)
        else none  -- Expected low surrogate but got something else.
      | [] => none  -- Truncated surrogate pair.
    else
      none  -- Unpaired low surrogate.
-- !benchmark @end code_aux def=absFromUTF16Checked

def Unicode.absFromUTF16Checked : Unicode.AbsFromUTF16CheckedSig :=
-- !benchmark @start code def=absFromUTF16Checked
  fun ws => (absFromUTF16Checked_decode ws).map String.ofList
-- !benchmark @end code def=absFromUTF16Checked
