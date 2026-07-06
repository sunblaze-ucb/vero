import Verdict.Impl.Validator

/-!
# Verdict.Test

Executable conformance tests. `#guard` assertions exercise the
curator's reference implementations.

DO NOT MODIFY — infrastructure.
-/

-- ── charToBits ────────────────────────────────────────────────
#guard Verdict.charToBits 0x41 = some (some 0)   -- 'A'
#guard Verdict.charToBits 0x5A = some (some 25)  -- 'Z'
#guard Verdict.charToBits 0x61 = some (some 26)  -- 'a'
#guard Verdict.charToBits 0x30 = some (some 52)  -- '0'
#guard Verdict.charToBits 0x39 = some (some 61)  -- '9'
#guard Verdict.charToBits 0x2B = some (some 62)  -- '+'
#guard Verdict.charToBits 0x2F = some (some 63)  -- '/'
#guard Verdict.charToBits 0x3D = some none       -- '='
#guard Verdict.charToBits 0x20 = none            -- ' '

-- ── decode6Bits (bit layout) ──────────────────────────────────
#guard Verdict.decode6Bits 0 0 0 0 = [0x00, 0x00, 0x00]
-- All-high 6-bit values: each output byte is 0xFF.
#guard Verdict.decode6Bits 63 63 63 63 = [0xFF, 0xFF, 0xFF]
-- First input shifts into byte 0 top bits.
#guard Verdict.decode6Bits 63 0 0 0 = [0xFC, 0x00, 0x00]
-- Last input lands in byte 2 low bits.
#guard Verdict.decode6Bits 0 0 0 63 = [0x00, 0x00, 0x3F]

-- ── decodeBase64 round-trip on a 4-char block ────────────────
-- "TWFu" = b"Man" in base64
#guard Verdict.decodeBase64 [0x54, 0x57, 0x46, 0x75] = some [0x4D, 0x61, 0x6E]
-- Empty input decodes to empty output.
#guard Verdict.decodeBase64 [] = some []
-- Odd length (not a multiple of 4) is rejected.
#guard Verdict.decodeBase64 [0x54] = none
#guard Verdict.decodeBase64 [0x54, 0x57, 0x46] = none
-- Padding `=` is NOT supported by the reference impl (see docstring).
-- Any `=` in a 4-char block falls through to `none`.
#guard Verdict.decodeBase64 [0x54, 0x57, 0x46, 0x3D] = none
-- Invalid characters (e.g. space) are rejected.
#guard Verdict.decodeBase64 [0x20, 0x57, 0x46, 0x75] = none

-- ── normalizeString (empty-only; `charLower` is opaque so any
--    non-empty input is not `decide`-reducible) ───────────────
#guard Verdict.normalizeString "" = ""

-- ── isSimplePath ──────────────────────────────────────────────
#guard Verdict.isSimplePath [] = true
#guard Verdict.isSimplePath [0] = true
#guard Verdict.isSimplePath [0, 1, 2] = true
#guard Verdict.isSimplePath [0, 1, 0] = false

-- ── pathInBounds ──────────────────────────────────────────────
#guard Verdict.pathInBounds [0, 1, 2] 3 = true
#guard Verdict.pathInBounds [0, 1, 3] 3 = false
#guard Verdict.pathInBounds [] 0 = true

-- ── chainFromPath ─────────────────────────────────────────────
#guard (Verdict.chainFromPath ([] : List Verdict.Certificate) [] default).length = 1
#guard (Verdict.chainFromPath
    ([default, default] : List Verdict.Certificate)
    [0, 1] default).length = 3

-- ── validateX509Base64 short-circuits on empty bundle ────────
#guard (Verdict.validateX509Base64 [] [] ⟨none, 0⟩).isOk = false
