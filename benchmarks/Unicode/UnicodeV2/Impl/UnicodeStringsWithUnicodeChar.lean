import UnicodeV2.Impl.Unicode

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Unicode.Impl.UnicodeStringsWithUnicodeChar

Conversion between Lean `String` values (--unicode-char:true mode) and
UTF-8 byte sequences (`List UInt8`) or UTF-16 code unit sequences (`List UInt16`).

In the `--unicode-char:true` mode, a Lean `String` is a sequence of Unicode
scalar values (surrogates are not valid `Char` values). The UTF-8 and UTF-16
encoding directions always succeed. The decoding directions may return `none`
when the input byte/code-unit sequence is malformed.

Types and signatures are fixed vocabulary (DO NOT MODIFY). Function bodies are
the curator's reference implementations; the pipeline replaces them with `sorry`
inside the `code` markers before presenting the benchmark to the LLM.
-/

namespace Unicode

-- ── API signatures (DO NOT MODIFY) ───────────────────────────────────────────

/-- Signature: convert a string (--unicode-char:true) to its UTF-8 byte representation. -/
abbrev UniCharToUTF8CheckedSig := String → Option (List UInt8)

/-- Signature: decode a UTF-8 byte sequence to a string (--unicode-char:true). -/
abbrev UniCharFromUTF8CheckedSig := List UInt8 → Option String

/-- Signature: convert a string (--unicode-char:true) to its UTF-16 code unit representation. -/
abbrev UniCharToUTF16CheckedSig := String → Option (List UInt16)

/-- Signature: decode a UTF-16 code unit sequence to a string (--unicode-char:true). -/
abbrev UniCharFromUTF16CheckedSig := List UInt16 → Option String

end Unicode

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- ── uniCharToUTF8Checked ─────────────────────────────────────────────────────

-- !benchmark @start code_aux def=uniCharToUTF8Checked
-- !benchmark @end code_aux def=uniCharToUTF8Checked

def Unicode.uniCharToUTF8Checked : Unicode.UniCharToUTF8CheckedSig :=
-- !benchmark @start code def=uniCharToUTF8Checked
  -- Lean 4 strings are always valid Unicode scalar-value sequences,
  -- so UTF-8 encoding always succeeds. Use the built-in toUTF8 method.
  fun s => some (s.toUTF8.data.toList)
-- !benchmark @end code def=uniCharToUTF8Checked

-- ── uniCharFromUTF8Checked ───────────────────────────────────────────────────

-- !benchmark @start code_aux def=uniCharFromUTF8Checked
-- !benchmark @end code_aux def=uniCharFromUTF8Checked

def Unicode.uniCharFromUTF8Checked : Unicode.UniCharFromUTF8CheckedSig :=
-- !benchmark @start code def=uniCharFromUTF8Checked
  -- Build a ByteArray from the byte list and attempt UTF-8 decoding.
  -- Returns none if the byte sequence is not valid UTF-8.
  fun bs => String.fromUTF8? ⟨bs.toArray⟩
-- !benchmark @end code def=uniCharFromUTF8Checked

-- ── uniCharToUTF16Checked ────────────────────────────────────────────────────

-- !benchmark @start code_aux def=uniCharToUTF16Checked
-- !benchmark @end code_aux def=uniCharToUTF16Checked

def Unicode.uniCharToUTF16Checked : Unicode.UniCharToUTF16CheckedSig :=
-- !benchmark @start code def=uniCharToUTF16Checked
  -- Encode each Lean Char as one or two UTF-16 code units.
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
-- !benchmark @end code def=uniCharToUTF16Checked

-- ── uniCharFromUTF16Checked ──────────────────────────────────────────────────

-- !benchmark @start code_aux def=uniCharFromUTF16Checked
-- Try to build a Char from a Unicode code-point value (Nat).
-- Returns none for surrogate code points or values above U+10FFFF.
private def uniCharFromUTF16Checked_charOfNat? (n : Nat) : Option Char :=
  let v := n.toUInt32
  if hv : v.isValidChar then some ⟨v, hv⟩ else none

-- Decode a list of UTF-16 code units into a list of Chars, returning
-- none if the sequence contains an unpaired or misplaced surrogate.
private def uniCharFromUTF16Checked_decode : List UInt16 → Option (List Char)
  | [] => some []
  | w :: rest =>
    let v := w.toNat
    if v < 0xD800 || v > 0xDFFF then
      -- Non-surrogate BMP character.
      (uniCharFromUTF16Checked_charOfNat? v).bind
        fun c => (uniCharFromUTF16Checked_decode rest).map (c :: ·)
    else if v ≤ 0xDBFF then
      -- High surrogate: must be followed by a low surrogate.
      match rest with
      | w2 :: rest2 =>
        let v2 := w2.toNat
        if v2 ≥ 0xDC00 && v2 ≤ 0xDFFF then
          let cp := 0x10000 + (v - 0xD800) * 0x400 + (v2 - 0xDC00)
          (uniCharFromUTF16Checked_charOfNat? cp).bind
            fun c => (uniCharFromUTF16Checked_decode rest2).map (c :: ·)
        else none  -- Expected low surrogate but got something else.
      | [] => none  -- Truncated surrogate pair.
    else
      none  -- Unpaired low surrogate.
-- !benchmark @end code_aux def=uniCharFromUTF16Checked

def Unicode.uniCharFromUTF16Checked : Unicode.UniCharFromUTF16CheckedSig :=
-- !benchmark @start code def=uniCharFromUTF16Checked
  fun ws => (uniCharFromUTF16Checked_decode ws).map String.ofList
-- !benchmark @end code def=uniCharFromUTF16Checked
