import UnicodeV2.Impl.Unicode

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Unicode.Impl.Utf8EncodingForm

UTF-8 encoding form for Unicode 14.0 (Table 3-6 / Table 3-7).
Maps each Unicode scalar value to a byte sequence of one to four unsigned
bytes. Well-formedness checks follow the bit patterns in Table 3-7 of the
Unicode Standard, Section 3.9.

Types and signatures are fixed vocabulary (DO NOT MODIFY). Function bodies
are the curator's reference implementations; the pipeline replaces them with
`sorry` inside the `code` markers before presenting the benchmark to the LLM.
-/

-- ── Type (DO NOT MODIFY) ──────────────────────────────────────────────────────

/-- A single UTF-8 code unit (one unsigned byte, 0x00–0xFF). -/
abbrev Utf8CodeUnit := UInt8

namespace Unicode

-- ── API signatures (DO NOT MODIFY) ───────────────────────────────────────────

abbrev Utf8IsMinimalWellFormedCodeUnitSubsequenceSig :=
  List Utf8CodeUnit → Bool

abbrev Utf8SplitPrefixMinimalWellFormedCodeUnitSubsequenceSig :=
  List Utf8CodeUnit → Option (List Utf8CodeUnit)

abbrev Utf8EncodeScalarValueSig :=
  ScalarValue → List Utf8CodeUnit

abbrev Utf8DecodeMinimalWellFormedCodeUnitSubsequenceSig :=
  List Utf8CodeUnit → ScalarValue

end Unicode

-- !benchmark @start global_aux

/-- The Unicode scalar value U+0000 (null), used as a fallback return value when
    the UTF-8 decode input is not a valid minimal well-formed sequence. -/
private def nullSV : ScalarValue :=
  ⟨⟨0, by decide⟩,
   ⟨Or.inl (by decide), Or.inl (by decide)⟩⟩

/-- Check that a 1-element byte list is a well-formed 1-byte UTF-8 sequence.
    Valid range for the leading byte: 0x00–0x7F. -/
private def utf8WellFormed1 : List UInt8 → Bool
  | [b0] => b0.toNat.ble 0x7F
  | _    => false

/-- Check that a 2-element byte list is a well-formed 2-byte UTF-8 sequence.
    Leading byte: 0xC2–0xDF; continuation byte: 0x80–0xBF. -/
private def utf8WellFormed2 : List UInt8 → Bool
  | [b0, b1] =>
    Nat.ble 0xC2 b0.toNat && b0.toNat.ble 0xDF &&
    Nat.ble 0x80 b1.toNat && b1.toNat.ble 0xBF
  | _ => false

/-- Check that a 3-element byte list is a well-formed 3-byte UTF-8 sequence
    per Table 3-7. The second-byte range depends on the leading byte:
    - 0xE0: 0xA0–0xBF; 0xE1–0xEC: 0x80–0xBF
    - 0xED: 0x80–0x9F; 0xEE–0xEF: 0x80–0xBF
    Third byte: 0x80–0xBF. -/
private def utf8WellFormed3 : List UInt8 → Bool
  | [b0, b1, b2] =>
    let n0 := b0.toNat
    let n1 := b1.toNat
    let n2 := b2.toNat
    ((n0 == 0xE0 && Nat.ble 0xA0 n1 && n1.ble 0xBF) ||
     (Nat.ble 0xE1 n0 && n0.ble 0xEC && Nat.ble 0x80 n1 && n1.ble 0xBF) ||
     (n0 == 0xED && Nat.ble 0x80 n1 && n1.ble 0x9F) ||
     (Nat.ble 0xEE n0 && n0.ble 0xEF && Nat.ble 0x80 n1 && n1.ble 0xBF)) &&
    Nat.ble 0x80 n2 && n2.ble 0xBF
  | _ => false

/-- Check that a 4-element byte list is a well-formed 4-byte UTF-8 sequence
    per Table 3-7. Second-byte range:
    - 0xF0: 0x90–0xBF; 0xF1–0xF3: 0x80–0xBF; 0xF4: 0x80–0x8F
    Third and fourth bytes: 0x80–0xBF. -/
private def utf8WellFormed4 : List UInt8 → Bool
  | [b0, b1, b2, b3] =>
    let n0 := b0.toNat
    let n1 := b1.toNat
    let n2 := b2.toNat
    let n3 := b3.toNat
    ((n0 == 0xF0 && Nat.ble 0x90 n1 && n1.ble 0xBF) ||
     (Nat.ble 0xF1 n0 && n0.ble 0xF3 && Nat.ble 0x80 n1 && n1.ble 0xBF) ||
     (n0 == 0xF4 && Nat.ble 0x80 n1 && n1.ble 0x8F)) &&
    Nat.ble 0x80 n2 && n2.ble 0xBF &&
    Nat.ble 0x80 n3 && n3.ble 0xBF
  | _ => false

-- !benchmark @end global_aux

-- !benchmark @start code_aux def=utf8IsMinimalWellFormedCodeUnitSubsequence
-- !benchmark @end code_aux def=utf8IsMinimalWellFormedCodeUnitSubsequence

def Unicode.utf8IsMinimalWellFormedCodeUnitSubsequence :
    Unicode.Utf8IsMinimalWellFormedCodeUnitSubsequenceSig :=
-- !benchmark @start code def=utf8IsMinimalWellFormedCodeUnitSubsequence
  fun s =>
    utf8WellFormed1 s || utf8WellFormed2 s || utf8WellFormed3 s || utf8WellFormed4 s
-- !benchmark @end code def=utf8IsMinimalWellFormedCodeUnitSubsequence

-- !benchmark @start code_aux def=utf8SplitPrefixMinimalWellFormedCodeUnitSubsequence
-- !benchmark @end code_aux def=utf8SplitPrefixMinimalWellFormedCodeUnitSubsequence

def Unicode.utf8SplitPrefixMinimalWellFormedCodeUnitSubsequence :
    Unicode.Utf8SplitPrefixMinimalWellFormedCodeUnitSubsequenceSig :=
-- !benchmark @start code def=utf8SplitPrefixMinimalWellFormedCodeUnitSubsequence
  fun s =>
    if Nat.ble 1 s.length && utf8WellFormed1 (s.take 1) then some (s.take 1)
    else if Nat.ble 2 s.length && utf8WellFormed2 (s.take 2) then some (s.take 2)
    else if Nat.ble 3 s.length && utf8WellFormed3 (s.take 3) then some (s.take 3)
    else if Nat.ble 4 s.length && utf8WellFormed4 (s.take 4) then some (s.take 4)
    else none
-- !benchmark @end code def=utf8SplitPrefixMinimalWellFormedCodeUnitSubsequence

-- !benchmark @start code_aux def=utf8EncodeScalarValue
-- !benchmark @end code_aux def=utf8EncodeScalarValue

def Unicode.utf8EncodeScalarValue : Unicode.Utf8EncodeScalarValueSig :=
-- !benchmark @start code def=utf8EncodeScalarValue
  fun v =>
    -- v.val : CodePoint = { i : Nat // i ≤ 0x10FFFF }, v.val.val : Nat
    let n := v.val.val
    if n.ble 0x7F then
      -- 1-byte: 0xxxxxxx
      [UInt8.ofNat (n &&& 0x7F)]
    else if n.ble 0x7FF then
      -- 2-byte: 110xxxxx 10xxxxxx
      [UInt8.ofNat (0xC0 ||| (n >>> 6)),
       UInt8.ofNat (0x80 ||| (n &&& 0x3F))]
    else if n.ble 0xFFFF then
      -- 3-byte: 1110xxxx 10xxxxxx 10xxxxxx
      [UInt8.ofNat (0xE0 ||| (n >>> 12)),
       UInt8.ofNat (0x80 ||| ((n >>> 6) &&& 0x3F)),
       UInt8.ofNat (0x80 ||| (n &&& 0x3F))]
    else
      -- 4-byte: 11110xxx 10xxxxxx 10xxxxxx 10xxxxxx
      [UInt8.ofNat (0xF0 ||| (n >>> 18)),
       UInt8.ofNat (0x80 ||| ((n >>> 12) &&& 0x3F)),
       UInt8.ofNat (0x80 ||| ((n >>> 6) &&& 0x3F)),
       UInt8.ofNat (0x80 ||| (n &&& 0x3F))]
-- !benchmark @end code def=utf8EncodeScalarValue

-- !benchmark @start code_aux def=utf8DecodeMinimalWellFormedCodeUnitSubsequence
-- !benchmark @end code_aux def=utf8DecodeMinimalWellFormedCodeUnitSubsequence

def Unicode.utf8DecodeMinimalWellFormedCodeUnitSubsequence :
    Unicode.Utf8DecodeMinimalWellFormedCodeUnitSubsequenceSig :=
-- !benchmark @start code def=utf8DecodeMinimalWellFormedCodeUnitSubsequence
  fun m =>
    -- Reconstruct the scalar value from the bit fields in the UTF-8 byte sequence.
    let n : Nat :=
      match m with
      | [b0] =>
        -- 1-byte: 0xxxxxxx → bits 0–6
        b0.toNat &&& 0x7F
      | [b0, b1] =>
        -- 2-byte: 110xxxxx 10xxxxxx → bits 6–10 from b0, bits 0–5 from b1
        ((b0.toNat &&& 0x1F) <<< 6) ||| (b1.toNat &&& 0x3F)
      | [b0, b1, b2] =>
        -- 3-byte: 1110xxxx 10xxxxxx 10xxxxxx
        ((b0.toNat &&& 0x0F) <<< 12) |||
        ((b1.toNat &&& 0x3F) <<< 6)  |||
        (b2.toNat &&& 0x3F)
      | [b0, b1, b2, b3] =>
        -- 4-byte: 11110xxx 10xxxxxx 10xxxxxx 10xxxxxx
        ((b0.toNat &&& 0x07) <<< 18) |||
        ((b1.toNat &&& 0x3F) <<< 12) |||
        ((b2.toNat &&& 0x3F) <<< 6)  |||
        (b3.toNat &&& 0x3F)
      | _ => 0
    -- Wrap the Nat into ScalarValue (subtype), falling back to U+0000 for invalid input.
    if h1 : n ≤ 0x10FFFF then
      if h2 : (n < HIGH_SURROGATE_MIN ∨ n > HIGH_SURROGATE_MAX) ∧
              (n < LOW_SURROGATE_MIN  ∨ n > LOW_SURROGATE_MAX) then
        ⟨⟨n, h1⟩, h2⟩
      else nullSV
    else nullSV
-- !benchmark @end code def=utf8DecodeMinimalWellFormedCodeUnitSubsequence
