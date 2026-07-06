import UnicodeV2.Impl.Unicode

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Unicode.Impl.Utf16EncodingForm

UTF-16 encoding form for Unicode 14.0 (Section 3.9 D91).

A UTF-16 code unit is a 16-bit unsigned integer. Scalar values in the BMP
(U+0000–U+D7FF and U+E000–U+FFFF) are encoded as a single code unit; scalar
values in supplementary planes (U+10000–U+10FFFF) are encoded as a high-surrogate
/ low-surrogate pair (Table 3-5).

Types and signatures are fixed vocabulary (DO NOT MODIFY). Function bodies are
the curator's reference implementations; the pipeline replaces them with `sorry`
inside the `code` markers before presenting the benchmark to the LLM.
-/

-- ── Type (DO NOT MODIFY) ─────────────────────────────────────────────────────

/-- A UTF-16 code unit: a 16-bit unsigned integer. (Section 3.9 D91) -/
abbrev Utf16CodeUnit := UInt16

namespace Unicode

-- ── API signatures (DO NOT MODIFY) ────────────────────────────────────────────

/-- Signature for testing whether a list of code units is a minimal well-formed
    UTF-16 code unit subsequence. -/
abbrev Utf16IsMinimalWellFormedCodeUnitSubsequenceSig :=
  List Utf16CodeUnit → Bool

/-- Signature for splitting the shortest well-formed UTF-16 prefix from a sequence. -/
abbrev Utf16SplitPrefixMinimalWellFormedCodeUnitSubsequenceSig :=
  List Utf16CodeUnit → Option (List Utf16CodeUnit)

/-- Signature for encoding a Unicode scalar value to its UTF-16 code unit sequence. -/
abbrev Utf16EncodeScalarValueSig :=
  ScalarValue → List Utf16CodeUnit

/-- Signature for decoding a minimal well-formed UTF-16 code unit sequence to a scalar value. -/
abbrev Utf16DecodeMinimalWellFormedCodeUnitSubsequenceSig :=
  List Utf16CodeUnit → ScalarValue

end Unicode

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- ── Implementation stubs (LLM task) ──────────────────────────────────────────

-- !benchmark @start code_aux def=utf16IsMinimalWellFormedCodeUnitSubsequence
-- !benchmark @end code_aux def=utf16IsMinimalWellFormedCodeUnitSubsequence

def Unicode.utf16IsMinimalWellFormedCodeUnitSubsequence
    : Unicode.Utf16IsMinimalWellFormedCodeUnitSubsequenceSig :=
-- !benchmark @start code def=utf16IsMinimalWellFormedCodeUnitSubsequence
  fun s =>
    match s with
    | [w] =>
      -- Single BMP code unit: not in surrogate range [0xD800, 0xDFFF]
      let v := w.toNat
      decide (v ≤ 0xD7FF) || decide (0xE000 ≤ v)
    | [w1, w2] =>
      -- High surrogate followed by low surrogate
      let v1 := w1.toNat
      let v2 := w2.toNat
      decide (0xD800 ≤ v1 ∧ v1 ≤ 0xDBFF) && decide (0xDC00 ≤ v2 ∧ v2 ≤ 0xDFFF)
    | _ => false
-- !benchmark @end code def=utf16IsMinimalWellFormedCodeUnitSubsequence

-- !benchmark @start code_aux def=utf16SplitPrefixMinimalWellFormedCodeUnitSubsequence
-- !benchmark @end code_aux def=utf16SplitPrefixMinimalWellFormedCodeUnitSubsequence

def Unicode.utf16SplitPrefixMinimalWellFormedCodeUnitSubsequence
    : Unicode.Utf16SplitPrefixMinimalWellFormedCodeUnitSubsequenceSig :=
-- !benchmark @start code def=utf16SplitPrefixMinimalWellFormedCodeUnitSubsequence
  fun s =>
    match s with
    | [] => none
    | [w] =>
      let v := w.toNat
      if decide (v ≤ 0xD7FF) || decide (0xE000 ≤ v) then some [w] else none
    | w1 :: w2 :: _ =>
      let v1 := w1.toNat
      -- Check if the first code unit is a valid single BMP code unit
      if decide (v1 ≤ 0xD7FF) || decide (0xE000 ≤ v1) then
        some [w1]
      else
        -- Check if the first two code units form a valid surrogate pair
        let v2 := w2.toNat
        if decide (0xD800 ≤ v1 ∧ v1 ≤ 0xDBFF) && decide (0xDC00 ≤ v2 ∧ v2 ≤ 0xDFFF) then
          some [w1, w2]
        else
          none
-- !benchmark @end code def=utf16SplitPrefixMinimalWellFormedCodeUnitSubsequence

-- !benchmark @start code_aux def=utf16EncodeScalarValue
-- !benchmark @end code_aux def=utf16EncodeScalarValue

def Unicode.utf16EncodeScalarValue : Unicode.Utf16EncodeScalarValueSig :=
-- !benchmark @start code def=utf16EncodeScalarValue
  fun v =>
    let n := v.val.val
    if n ≤ 0xD7FF ∨ (0xE000 ≤ n ∧ n ≤ 0xFFFF) then
      -- Single BMP code unit: cast the scalar value directly to UInt16
      [n.toUInt16]
    else
      -- Surrogate pair for supplementary planes (n ∈ [0x10000, 0x10FFFF])
      -- See Unicode Table 3-5: UTF-16 Bit Distribution
      --   v = 000u uuuu xxxx xxxx xxxx xxxx  (u = plane, x = offset bits)
      let x2 := n &&& 0x3FF           -- lower 10 bits
      let x1 := (n &&& 0xFC00) >>> 10 -- bits 10–15 (6 bits)
      let u  := (n &&& 0x1F0000) >>> 16 -- bits 16–20 (plane number, 1–16)
      let w  := u - 1                 -- 4-bit value (0–15)
      -- high surrogate: 1101 10ww wwxx xxxx  (0xD800–0xDBFF)
      let high := 0xD800 ||| (w <<< 6) ||| x1
      -- low surrogate:  1101 11xx xxxx xxxx  (0xDC00–0xDFFF)
      let low  := 0xDC00 ||| x2
      [high.toUInt16, low.toUInt16]
-- !benchmark @end code def=utf16EncodeScalarValue

-- !benchmark @start code_aux def=utf16DecodeMinimalWellFormedCodeUnitSubsequence
-- !benchmark @end code_aux def=utf16DecodeMinimalWellFormedCodeUnitSubsequence

def Unicode.utf16DecodeMinimalWellFormedCodeUnitSubsequence
    : Unicode.Utf16DecodeMinimalWellFormedCodeUnitSubsequenceSig :=
-- !benchmark @start code def=utf16DecodeMinimalWellFormedCodeUnitSubsequence
  fun s =>
    -- Default: U+0000 (NUL), used for malformed inputs
    let default : ScalarValue := ⟨⟨0, by decide⟩, by decide⟩
    match s with
    | [w] =>
      -- Single BMP code unit: the code unit value is the scalar value
      let n := w.toNat
      if h1 : n ≤ 0x10FFFF then
        let cp : CodePoint := ⟨n, h1⟩
        if h2 : (cp.val < HIGH_SURROGATE_MIN ∨ cp.val > HIGH_SURROGATE_MAX) ∧
                (cp.val < LOW_SURROGATE_MIN  ∨ cp.val > LOW_SURROGATE_MAX) then
          ⟨cp, h2⟩
        else
          default  -- surrogate code unit: malformed input
      else
        default  -- impossible for UInt16, but required for totality
    | [w1, w2] =>
      -- Surrogate pair: decode via UTF-16 bit distribution (Table 3-5)
      let v1 := w1.toNat
      let v2 := w2.toNat
      let x2     := v2 &&& 0x3FF          -- lower 10 bits of low surrogate
      let x1     := v1 &&& 0x3F           -- lower 6 bits of high surrogate
      let ww     := (v1 &&& 0x3C0) >>> 6  -- bits 6–9 of high surrogate (4 bits)
      let u      := ww + 1                -- plane number (1–16)
      let result := (u <<< 16) ||| (x1 <<< 10) ||| x2
      if h1 : result ≤ 0x10FFFF then
        let cp : CodePoint := ⟨result, h1⟩
        if h2 : (cp.val < HIGH_SURROGATE_MIN ∨ cp.val > HIGH_SURROGATE_MAX) ∧
                (cp.val < LOW_SURROGATE_MIN  ∨ cp.val > LOW_SURROGATE_MAX) then
          ⟨cp, h2⟩
        else
          default  -- malformed surrogate pair
      else
        default  -- result out of Unicode range: malformed input
    | _ => default  -- wrong length: malformed input
-- !benchmark @end code def=utf16DecodeMinimalWellFormedCodeUnitSubsequence
