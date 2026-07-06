import Base58.Impl.Codec

/-!
# Base58.Test

Executable conformance tests. `#guard` assertions run against the curator's
reference implementations inside the `code` markers in `Impl/Codec.lean`.

DO NOT MODIFY — infrastructure.
-/

open Base58

-- ── decodeInt: positional value over the frozen alphabet ─────────
#guard decodeInt "" == some 0                 -- empty fold base case
#guard decodeInt "z" == some 57               -- last alphabet char
#guard decodeInt "21" == some 58              -- 1*58 + 0
#guard decodeInt "5R" == some 256             -- 4*58 + 24
#guard decodeInt "0" == none                  -- '0' not in alphabet

-- ── encodeInt: canonical numeral via div/mod-58 ──────────────────
#guard encodeInt 0 == "1"                     -- the zero digit
#guard encodeInt 57 == "z"
#guard encodeInt 58 == "21"
#guard encodeInt 256 == "5R"
#guard encodeInt 3471844090 == "6Ho7Hs"

-- ── encode: leading-zero boundary ────────────────────────────────
#guard encode [0, 0, 1] == "112"              -- two leading zero bytes → "11"
#guard encode ([] : Bytes) == ""
#guard encode [255] == "5Q"
#guard encode [0, 255] == "15Q"               -- one leading zero byte → "1"

-- ── decode: inverse of encode ────────────────────────────────────
#guard decode "112" == some [0, 0, 1]
#guard decode "5Q" == some [255]
#guard decode "0" == none                     -- invalid char rejected
#guard decode (encode [0, 0, 42, 7]) == some [0, 0, 42, 7]   -- round trip
