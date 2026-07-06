import UnicodeV2.Impl.Utf16EncodingForm

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Unicode.Impl.UnicodeStringsWithoutUnicodeChar

Conversion between the `--unicode-char:false` Dafny string model (a raw
`List UInt16` of UTF-16 code units, not guaranteed to be valid Unicode) and
UTF-8 byte sequences or validated UTF-16 code unit sequences.

In the `--unicode-char:false` model a Dafny `string` is simply `seq<uint16>`,
so all four entry points take or return `List UInt16` rather than a Lean
`String`. Well-formedness is validated at the boundary and reported via `Option`.

Types and signatures are fixed vocabulary (DO NOT MODIFY). Function bodies are
the curator's reference implementations; the pipeline replaces them with `sorry`
inside the `code` markers before presenting the benchmark to the LLM.
-/

namespace Unicode

-- ── API signatures (DO NOT MODIFY) ────────────────────────────────────────────

/-- Signature: convert a raw UTF-16 code unit sequence to UTF-8 bytes. -/
abbrev NoCharToUTF8CheckedSig := List UInt16 → Option (List UInt8)

/-- Signature: decode a UTF-8 byte sequence to a raw UTF-16 code unit sequence. -/
abbrev NoCharFromUTF8CheckedSig := List UInt8 → Option (List UInt16)

/-- Signature: validate and return a raw UTF-16 code unit sequence unchanged. -/
abbrev NoCharToUTF16CheckedSig := List UInt16 → Option (List UInt16)

/-- Signature: validate a `uint16` sequence as well-formed UTF-16 and return it. -/
abbrev NoCharFromUTF16CheckedSig := List UInt16 → Option (List UInt16)

end Unicode

-- !benchmark @start global_aux

/-! ## Private helpers shared by multiple APIs -/

/-- Attempt to construct a `ScalarValue` from a raw code-point `Nat`.
    Returns `none` if `n` is outside the Unicode codespace or in the
    surrogate range (U+D800–U+DFFF). -/
private def noChar_mkScalarValue? (n : Nat) : Option ScalarValue :=
  if h1 : n ≤ 0x10FFFF then
    let cp : CodePoint := ⟨n, h1⟩
    if h2 : (cp.val < HIGH_SURROGATE_MIN ∨ cp.val > HIGH_SURROGATE_MAX) ∧
            (cp.val < LOW_SURROGATE_MIN  ∨ cp.val > LOW_SURROGATE_MAX) then
      some ⟨cp, h2⟩
    else none
  else none

/-- Decode a `List UInt16` raw UTF-16 code unit sequence into `List ScalarValue`.
    Returns `none` if the sequence is not well-formed UTF-16 (e.g. an unpaired
    surrogate or a lone low surrogate). -/
private def noChar_decodeUtf16 : List UInt16 → Option (List ScalarValue)
  | [] => some []
  | w :: rest =>
    let v := w.toNat
    if v ≤ 0xD7FF || 0xE000 ≤ v then
      -- Non-surrogate BMP character (U+0000–U+D7FF or U+E000–U+FFFF).
      -- UInt16 guarantees v ≤ 0xFFFF ≤ 0x10FFFF, and v is outside the
      -- surrogate range, so mkScalarValue? always returns `some` here.
      (noChar_mkScalarValue? v).bind fun sv =>
        (noChar_decodeUtf16 rest).map (sv :: ·)
    else if 0xD800 ≤ v && v ≤ 0xDBFF then
      -- High surrogate: must be immediately followed by a low surrogate.
      match rest with
      | w2 :: rest2 =>
        let v2 := w2.toNat
        if 0xDC00 ≤ v2 && v2 ≤ 0xDFFF then
          -- Decode the surrogate pair (Unicode Table 3-5).
          let x2 := v2 &&& 0x3FF          -- lower 10 bits of low surrogate
          let x1 := v  &&& 0x3F           -- lower 6 bits of high surrogate
          let ww := (v &&& 0x3C0) >>> 6   -- bits 6–9 of high surrogate (4 bits)
          let u  := ww + 1                 -- plane number (1–16)
          let n  := (u <<< 16) ||| (x1 <<< 10) ||| x2
          (noChar_mkScalarValue? n).bind fun sv =>
            (noChar_decodeUtf16 rest2).map (sv :: ·)
        else none  -- expected low surrogate, got something else
      | [] => none   -- truncated surrogate pair
    else none  -- low surrogate without a preceding high surrogate
termination_by s => s.length

/-- Encode a single `ScalarValue` to its UTF-8 byte representation.
    Implements the UTF-8 encoding algorithm from Unicode Table 3-6. -/
private def noChar_encodeScalarUtf8 (sv : ScalarValue) : List UInt8 :=
  let n := sv.val.val
  if n ≤ 0x7F then
    -- 1 byte: 0xxxxxxx
    [n.toUInt8]
  else if n ≤ 0x7FF then
    -- 2 bytes: 110xxxxx 10xxxxxx
    [(0xC0 ||| (n >>> 6)).toUInt8,
     (0x80 ||| (n &&& 0x3F)).toUInt8]
  else if n ≤ 0xFFFF then
    -- 3 bytes: 1110xxxx 10xxxxxx 10xxxxxx
    [(0xE0 ||| (n >>> 12)).toUInt8,
     (0x80 ||| ((n >>> 6) &&& 0x3F)).toUInt8,
     (0x80 ||| (n &&& 0x3F)).toUInt8]
  else
    -- 4 bytes: 11110xxx 10xxxxxx 10xxxxxx 10xxxxxx
    [(0xF0 ||| (n >>> 18)).toUInt8,
     (0x80 ||| ((n >>> 12) &&& 0x3F)).toUInt8,
     (0x80 ||| ((n >>> 6) &&& 0x3F)).toUInt8,
     (0x80 ||| (n &&& 0x3F)).toUInt8]

/-- Decode a UTF-8 byte sequence into a list of Unicode scalar values.
    Returns `none` if any byte sub-sequence is not valid UTF-8.
    Implements the validity rules from Unicode Table 3-7. -/
private def noChar_decodeUtf8 : List UInt8 → Option (List ScalarValue)
  | [] => some []
  | b :: rest =>
    let v := b.toNat
    if v ≤ 0x7F then
      -- 1-byte (ASCII): 0x00–0x7F
      (noChar_mkScalarValue? v).bind fun sv =>
        (noChar_decodeUtf8 rest).map (sv :: ·)
    else if 0xC2 ≤ v && v ≤ 0xDF then
      -- 2-byte: 0xC2–0xDF followed by 0x80–0xBF
      match rest with
      | b2 :: rest2 =>
        let v2 := b2.toNat
        if 0x80 ≤ v2 && v2 ≤ 0xBF then
          let n := ((v &&& 0x1F) <<< 6) ||| (v2 &&& 0x3F)
          (noChar_mkScalarValue? n).bind fun sv =>
            (noChar_decodeUtf8 rest2).map (sv :: ·)
        else none
      | [] => none
    else if v == 0xE0 then
      -- 3-byte starting 0xE0: second byte must be 0xA0–0xBF (avoid overlong)
      match rest with
      | b2 :: b3 :: rest3 =>
        let v2 := b2.toNat; let v3 := b3.toNat
        if 0xA0 ≤ v2 && v2 ≤ 0xBF && 0x80 ≤ v3 && v3 ≤ 0xBF then
          let n := ((v &&& 0xF) <<< 12) ||| ((v2 &&& 0x3F) <<< 6) ||| (v3 &&& 0x3F)
          (noChar_mkScalarValue? n).bind fun sv =>
            (noChar_decodeUtf8 rest3).map (sv :: ·)
        else none
      | _ => none
    else if 0xE1 ≤ v && v ≤ 0xEC then
      -- 3-byte starting 0xE1–0xEC: second byte 0x80–0xBF
      match rest with
      | b2 :: b3 :: rest3 =>
        let v2 := b2.toNat; let v3 := b3.toNat
        if 0x80 ≤ v2 && v2 ≤ 0xBF && 0x80 ≤ v3 && v3 ≤ 0xBF then
          let n := ((v &&& 0xF) <<< 12) ||| ((v2 &&& 0x3F) <<< 6) ||| (v3 &&& 0x3F)
          (noChar_mkScalarValue? n).bind fun sv =>
            (noChar_decodeUtf8 rest3).map (sv :: ·)
        else none
      | _ => none
    else if v == 0xED then
      -- 3-byte starting 0xED: second byte 0x80–0x9F (avoid encoding surrogates)
      match rest with
      | b2 :: b3 :: rest3 =>
        let v2 := b2.toNat; let v3 := b3.toNat
        if 0x80 ≤ v2 && v2 ≤ 0x9F && 0x80 ≤ v3 && v3 ≤ 0xBF then
          let n := ((v &&& 0xF) <<< 12) ||| ((v2 &&& 0x3F) <<< 6) ||| (v3 &&& 0x3F)
          (noChar_mkScalarValue? n).bind fun sv =>
            (noChar_decodeUtf8 rest3).map (sv :: ·)
        else none
      | _ => none
    else if 0xEE ≤ v && v ≤ 0xEF then
      -- 3-byte starting 0xEE–0xEF: second byte 0x80–0xBF
      match rest with
      | b2 :: b3 :: rest3 =>
        let v2 := b2.toNat; let v3 := b3.toNat
        if 0x80 ≤ v2 && v2 ≤ 0xBF && 0x80 ≤ v3 && v3 ≤ 0xBF then
          let n := ((v &&& 0xF) <<< 12) ||| ((v2 &&& 0x3F) <<< 6) ||| (v3 &&& 0x3F)
          (noChar_mkScalarValue? n).bind fun sv =>
            (noChar_decodeUtf8 rest3).map (sv :: ·)
        else none
      | _ => none
    else if v == 0xF0 then
      -- 4-byte starting 0xF0: second byte 0x90–0xBF (avoid overlong)
      match rest with
      | b2 :: b3 :: b4 :: rest4 =>
        let v2 := b2.toNat; let v3 := b3.toNat; let v4 := b4.toNat
        if 0x90 ≤ v2 && v2 ≤ 0xBF && 0x80 ≤ v3 && v3 ≤ 0xBF && 0x80 ≤ v4 && v4 ≤ 0xBF then
          let n := ((v &&& 0x7) <<< 18) ||| ((v2 &&& 0x3F) <<< 12) |||
                   ((v3 &&& 0x3F) <<< 6)  ||| (v4 &&& 0x3F)
          (noChar_mkScalarValue? n).bind fun sv =>
            (noChar_decodeUtf8 rest4).map (sv :: ·)
        else none
      | _ => none
    else if 0xF1 ≤ v && v ≤ 0xF3 then
      -- 4-byte starting 0xF1–0xF3: second byte 0x80–0xBF
      match rest with
      | b2 :: b3 :: b4 :: rest4 =>
        let v2 := b2.toNat; let v3 := b3.toNat; let v4 := b4.toNat
        if 0x80 ≤ v2 && v2 ≤ 0xBF && 0x80 ≤ v3 && v3 ≤ 0xBF && 0x80 ≤ v4 && v4 ≤ 0xBF then
          let n := ((v &&& 0x7) <<< 18) ||| ((v2 &&& 0x3F) <<< 12) |||
                   ((v3 &&& 0x3F) <<< 6)  ||| (v4 &&& 0x3F)
          (noChar_mkScalarValue? n).bind fun sv =>
            (noChar_decodeUtf8 rest4).map (sv :: ·)
        else none
      | _ => none
    else if v == 0xF4 then
      -- 4-byte starting 0xF4: second byte 0x80–0x8F (capped to U+10FFFF)
      match rest with
      | b2 :: b3 :: b4 :: rest4 =>
        let v2 := b2.toNat; let v3 := b3.toNat; let v4 := b4.toNat
        if 0x80 ≤ v2 && v2 ≤ 0x8F && 0x80 ≤ v3 && v3 ≤ 0xBF && 0x80 ≤ v4 && v4 ≤ 0xBF then
          let n := ((v &&& 0x7) <<< 18) ||| ((v2 &&& 0x3F) <<< 12) |||
                   ((v3 &&& 0x3F) <<< 6)  ||| (v4 &&& 0x3F)
          (noChar_mkScalarValue? n).bind fun sv =>
            (noChar_decodeUtf8 rest4).map (sv :: ·)
        else none
      | _ => none
    else
      none  -- invalid lead byte
termination_by bs => bs.length

/-- Test whether a `List UInt16` is a well-formed UTF-16 code unit sequence.
    Returns `true` iff every code unit is either a non-surrogate BMP value or
    part of a valid high-surrogate / low-surrogate pair. -/
private def noChar_isWellFormedUtf16 : List UInt16 → Bool
  | [] => true
  | w :: rest =>
    let v := w.toNat
    if v ≤ 0xD7FF || 0xE000 ≤ v then
      -- Non-surrogate BMP code unit.
      noChar_isWellFormedUtf16 rest
    else if 0xD800 ≤ v && v ≤ 0xDBFF then
      -- High surrogate: consume the following low surrogate.
      match rest with
      | w2 :: rest2 =>
        let v2 := w2.toNat
        0xDC00 ≤ v2 && v2 ≤ 0xDFFF && noChar_isWellFormedUtf16 rest2
      | [] => false
    else
      false  -- lone low surrogate
termination_by s => s.length

-- !benchmark @end global_aux

-- ── noCharToUTF8Checked ───────────────────────────────────────────────────────

-- !benchmark @start code_aux def=noCharToUTF8Checked
-- !benchmark @end code_aux def=noCharToUTF8Checked

def Unicode.noCharToUTF8Checked : Unicode.NoCharToUTF8CheckedSig :=
-- !benchmark @start code def=noCharToUTF8Checked
  -- Decode the raw UTF-16 code unit sequence into scalar values (returns none
  -- if the sequence is not well-formed UTF-16), then encode each scalar value
  -- as UTF-8 and flatten the result into a byte list.
  fun s =>
    (noChar_decodeUtf16 s).map fun scalars =>
      scalars.flatMap noChar_encodeScalarUtf8
-- !benchmark @end code def=noCharToUTF8Checked

-- ── noCharFromUTF8Checked ─────────────────────────────────────────────────────

-- !benchmark @start code_aux def=noCharFromUTF8Checked
-- !benchmark @end code_aux def=noCharFromUTF8Checked

def Unicode.noCharFromUTF8Checked : Unicode.NoCharFromUTF8CheckedSig :=
-- !benchmark @start code def=noCharFromUTF8Checked
  -- Decode the UTF-8 byte sequence into scalar values (returns none if the
  -- bytes are not valid UTF-8), then encode each scalar value as UTF-16
  -- code units and flatten into a List UInt16.
  fun bs =>
    (noChar_decodeUtf8 bs).map fun scalars =>
      scalars.flatMap Unicode.utf16EncodeScalarValue
-- !benchmark @end code def=noCharFromUTF8Checked

-- ── noCharToUTF16Checked ──────────────────────────────────────────────────────

-- !benchmark @start code_aux def=noCharToUTF16Checked
-- !benchmark @end code_aux def=noCharToUTF16Checked

def Unicode.noCharToUTF16Checked : Unicode.NoCharToUTF16CheckedSig :=
-- !benchmark @start code def=noCharToUTF16Checked
  -- Validate that the raw UTF-16 code unit sequence is well-formed.
  -- If valid, return it unchanged; otherwise return none.
  fun s =>
    if noChar_isWellFormedUtf16 s then some s else none
-- !benchmark @end code def=noCharToUTF16Checked

-- ── noCharFromUTF16Checked ────────────────────────────────────────────────────

-- !benchmark @start code_aux def=noCharFromUTF16Checked
-- !benchmark @end code_aux def=noCharFromUTF16Checked

def Unicode.noCharFromUTF16Checked : Unicode.NoCharFromUTF16CheckedSig :=
-- !benchmark @start code def=noCharFromUTF16Checked
  -- Validate that the uint16 code unit sequence is well-formed UTF-16.
  -- If valid, return it as a raw UTF-16 sequence; otherwise return none.
  fun bs =>
    if noChar_isWellFormedUtf16 bs then some bs else none
-- !benchmark @end code def=noCharFromUTF16Checked
