import Bmpwriter.Impl.Image

/-!
# Bmpwriter.Test

Executable conformance tests. `#guard` assertions run against the curator's
reference implementations inside the `code` markers in `Impl/Image.lean`.

DO NOT MODIFY — infrastructure.
-/

open Bmpwriter

-- ── build: exact layout (7-byte header ++ payload) ──────────────
#guard build 1 1 [255] == [82, 71, 66, 0, 1, 0, 1, 255]
#guard build 258 3 [9, 9] == [82, 71, 66, 1, 2, 0, 3, 9, 9]   -- 258 = 1*256 + 2
#guard build 0 0 [] == [82, 71, 66, 0, 0, 0, 0]
#guard (build 7 2 [1, 2, 3]).length == 7 + 3                  -- length = 7 + payload

-- ── validMagic: three-byte prefix check ─────────────────────────
#guard validMagic [82, 71, 66, 0, 0] == true
#guard validMagic [82, 71, 67] == false                        -- 'C' not 'B'
#guard validMagic ([] : List UInt8) == false
#guard validMagic (build 5 5 [42]) == true                     -- built always valid

-- ── parseWidth: independent big-endian decode of bytes 3,4 ──────
#guard parseWidth [82, 71, 66, 1, 2, 0, 3] == some 258         -- 1*256 + 2
#guard parseWidth [0, 0, 0, 0, 5] == some 5                    -- decode ignores magic
#guard parseWidth [1, 2, 3] == none                            -- too short (< 5)

-- ── parseHeight: independent big-endian decode of bytes 5,6 ─────
#guard parseHeight [82, 71, 66, 1, 2, 0, 3] == some 3          -- 0*256 + 3
#guard parseHeight [0, 0, 0, 0, 0, 1, 4] == some 260           -- 1*256 + 4
#guard parseHeight [82, 71, 66, 1, 2, 0] == none               -- too short (< 7)

-- ── parse: magic check + field extraction ───────────────────────
#guard parse (build 258 3 [9, 9]) == some (258, 3, [9, 9])     -- round-trip in range
#guard parse [82, 71, 67, 1, 2, 0, 3] == none                  -- bad magic
#guard parse [82, 71, 66, 1, 2, 0] == none                     -- truncated header
#guard parse [82, 71, 66, 0, 5, 0, 7, 11, 22] == some (5, 7, [11, 22])

-- ── structural laws over the serialize / parse relation ─────────
-- build is one-to-one on the in-range domain (distinct inputs ⇒ distinct bytes)
#guard build 258 3 [9, 9] != build 259 3 [9, 9]               -- width differs
#guard build 258 3 [9, 9] != build 258 3 [9, 8]               -- payload differs
-- parse is a left inverse of build on its success domain
#guard (parse [82, 71, 66, 1, 2, 0, 3, 9, 9]).map (fun t => build t.1 t.2.1 t.2.2)
         == some [82, 71, 66, 1, 2, 0, 3, 9, 9]
-- recovered payload is the input past the 7-byte header
#guard (parse [82, 71, 66, 0, 5, 0, 7, 11, 22]).map (fun t => t.2.2) == some [11, 22]
-- accepted input ⇒ width / height agree with the independent decoders
#guard (parse [82, 71, 66, 1, 2, 0, 7, 11]).map (fun t => t.1)
         == parseWidth [82, 71, 66, 1, 2, 0, 7, 11]
#guard (parse [82, 71, 66, 1, 2, 0, 7, 11]).map (fun t => t.2.1)
         == parseHeight [82, 71, 66, 1, 2, 0, 7, 11]
-- length law on success: len = 7 + payload length
#guard (parse [82, 71, 66, 0, 5, 0, 7, 11, 22, 33]).map (fun t => 7 + t.2.2.length)
         == some [82, 71, 66, 0, 5, 0, 7, 11, 22, 33].length

-- ── whole-relation laws over arbitrary byte lists ───────────────
-- header observations depend only on the first 7 bytes (differ only past byte 6)
#guard parseWidth [82, 71, 66, 1, 2, 0, 7, 99] == parseWidth [82, 71, 66, 1, 2, 0, 7, 42, 43]
#guard parseHeight [82, 71, 66, 1, 2, 0, 7, 99] == parseHeight [82, 71, 66, 1, 2, 0, 7, 42, 43]
#guard validMagic [82, 71, 66, 1, 2, 0, 7, 99] == validMagic [82, 71, 66, 1, 2, 0, 7, 42, 43]
-- trailing bytes extend the payload, fields unchanged
#guard parse ([82, 71, 66, 0, 5, 0, 7, 11] ++ [22, 33]) == some (5, 7, [11, 22, 33])
-- parse succeeds iff bytes are an in-range built image; recovered fields rebuild it
#guard (parse (build 258 3 [9, 9])).map (fun t => build t.1 t.2.1 t.2.2) == some (build 258 3 [9, 9])
-- decoded dimensions always fit in 16 bits
#guard (parseWidth [82, 71, 66, 255, 255, 0, 0]).map (fun w => decide (w < 65536)) == some true
#guard (parseHeight [82, 71, 66, 0, 0, 255, 255]).map (fun h => decide (h < 65536)) == some true
