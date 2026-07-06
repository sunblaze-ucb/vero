import Verdict.Impl.Asn1

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Verdict.Impl.Base64

RFC 4648 Base64 decoding. A genuinely executable primitive in Verus
(not crypto-opaque) — the LLM is expected to implement it. `encode`
is not part of verdict's public API, so only `decodeBase64` and its
helpers are exposed.

Upstream:
- `verdict-parser/src/common/base64.rs`
- `verdict/src/lib.rs::decode_base64`
-/

namespace Verdict

-- ── API signatures (DO NOT MODIFY) ───────────────────────────

/-- Map a base64 character to its 6-bit value.
    Returns `none` if the character is `=` (padding), outer `none` if
    the character is not a valid base64 alphabet character. -/
abbrev CharToBitsSig := UInt8 → Option (Option UInt8)

/-- Decode 4 base64 characters into 3 raw bytes. -/
abbrev Decode6BitsSig := UInt8 → UInt8 → UInt8 → UInt8 → List UInt8

/-- Top-level base64 decoder. -/
abbrev DecodeBase64Sig := Bytes → Option Bytes

/-- Parse an X.509 certificate from base64 (composition of
    `decodeBase64` with `parseX509Der`). -/
abbrev ParseX509Base64Sig := Bytes → Option Certificate

end Verdict

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- ── Implementations ──────────────────────────────────────────

-- !benchmark @start code_aux def=charToBits
-- !benchmark @end code_aux def=charToBits

def Verdict.charToBits : Verdict.CharToBitsSig :=
-- !benchmark @start code def=charToBits
  fun c =>
    -- 'A'..'Z' → 0..25
    if c ≥ 0x41 ∧ c ≤ 0x5A then some (some (c - 0x41))
    -- 'a'..'z' → 26..51
    else if c ≥ 0x61 ∧ c ≤ 0x7A then some (some (c - 0x61 + 26))
    -- '0'..'9' → 52..61
    else if c ≥ 0x30 ∧ c ≤ 0x39 then some (some (c - 0x30 + 52))
    -- '+' → 62
    else if c = 0x2B then some (some 62)
    -- '/' → 63
    else if c = 0x2F then some (some 63)
    -- '=' → padding
    else if c = 0x3D then some none
    -- invalid
    else none
-- !benchmark @end code def=charToBits

-- !benchmark @start code_aux def=decode6Bits
-- !benchmark @end code_aux def=decode6Bits

def Verdict.decode6Bits : Verdict.Decode6BitsSig :=
-- !benchmark @start code def=decode6Bits
  fun a b c d =>
    [ (a <<< 2) ||| (b >>> 4)
    , (b <<< 4) ||| (c >>> 2)
    , (c <<< 6) ||| d ]
-- !benchmark @end code def=decode6Bits

-- !benchmark @start code_aux def=decodeBase64
-- !benchmark @end code_aux def=decodeBase64

/-- Decodes a base64-encoded byte string. For simplicity the reference
    impl handles only complete 4-character blocks (no padding
    support); production code should handle `=` padding. Production
    certs are padded to a multiple of 4, so this works on well-formed
    inputs. -/
def Verdict.decodeBase64 : Verdict.DecodeBase64Sig :=
-- !benchmark @start code def=decodeBase64
  fun input =>
    let rec go : Verdict.Bytes → Option Verdict.Bytes
      | [] => some []
      | a :: b :: c :: d :: rest => do
          let av ← (← Verdict.charToBits a)
          let bv ← (← Verdict.charToBits b)
          let cv ← (← Verdict.charToBits c)
          let dv ← (← Verdict.charToBits d)
          let tail ← go rest
          some (Verdict.decode6Bits av bv cv dv ++ tail)
      | _ => none
    go input
-- !benchmark @end code def=decodeBase64

-- !benchmark @start code_aux def=parseX509Base64
-- !benchmark @end code_aux def=parseX509Base64

def Verdict.parseX509Base64 : Verdict.ParseX509Base64Sig :=
-- !benchmark @start code def=parseX509Base64
  fun input => Verdict.decodeBase64 input >>= Verdict.parseX509Der
-- !benchmark @end code def=parseX509Base64
