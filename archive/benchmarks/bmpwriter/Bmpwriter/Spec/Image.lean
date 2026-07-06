import Bmpwriter.Harness

/-!
# Bmpwriter.Spec.Image

Specifications for the fixed-schema image writer/parser. Each `spec_*` is a
property over an arbitrary `impl : RepoImpl`; an API is always reached through
`impl.bmpwriter.<fn>`, never by calling `Bmpwriter.<fn>` directly.

The two directions are pinned independently:

* **`build` — exact byte layout.** `spec_build_layout_exact` states the output
  equals `[82,71,66, w/256, w%256, h/256, h%256] ++ px` byte for byte.

* **`parse` — big-endian decode.** `spec_parse_width_decode` and
  `spec_parse_height_decode` pin `parseWidth` / `parseHeight` to
  `hi.toNat·256 + lo.toNat` of their own header bytes, on an arbitrary byte
  list.

The magic tag `[82, 71, 66]` and the 7-byte header width never refer to
`impl`.

DO NOT MODIFY — frozen spec.
-/

-- ════════════════════════════════════════════════════════════════
-- build: exact byte layout
-- ════════════════════════════════════════════════════════════════

/-- Exact-layout law: the serialized form is the concatenation of the 7-byte
    header and the payload — `[82,71,66, w/256, w%256, h/256, h%256] ++ px`,
    byte for byte. -/
def spec_build_layout_exact (impl : RepoImpl) : Prop :=
  ∀ (w h : Nat) (px : List UInt8),
    impl.bmpwriter.build w h px
      = [82, 71, 66, (w / 256).toUInt8, (w % 256).toUInt8,
         (h / 256).toUInt8, (h % 256).toUInt8] ++ px

/-- Header byte count: the serialized length is exactly `7 + px.length` — a
    seven-byte header and the payload appended verbatim with no padding. -/
def spec_build_length (impl : RepoImpl) : Prop :=
  ∀ (w h : Nat) (px : List UInt8),
    (impl.bmpwriter.build w h px).length = 7 + px.length

/-- The serialized form always begins with the three magic bytes `[82,71,66]`,
    regardless of `w`, `h`, or the payload — the magic prefix is `take 3` of any
    built byte list. Pins the leading tag. -/
def spec_build_magic_prefix (impl : RepoImpl) : Prop :=
  ∀ (w h : Nat) (px : List UInt8),
    (impl.bmpwriter.build w h px).take 3 = [82, 71, 66]

/-- The payload occupies the tail of the serialized form: dropping the 7-byte
    header recovers the original pixel bytes verbatim. The other half of the
    7-byte-header pinning — `drop 7` is exactly the payload. -/
def spec_build_payload_tail (impl : RepoImpl) : Prop :=
  ∀ (w h : Nat) (px : List UInt8),
    (impl.bmpwriter.build w h px).drop 7 = px

-- ════════════════════════════════════════════════════════════════
-- parseWidth / parseHeight: big-endian decode
-- ════════════════════════════════════════════════════════════════

/-- Width decode: on any byte list whose bytes 3 and 4 are present, `parseWidth`
    returns the 16-bit big-endian value `byte₃·256 + byte₄`. Stated on an
    arbitrary list, not via `build`. -/
def spec_parse_width_decode (impl : RepoImpl) : Prop :=
  ∀ (b0 b1 b2 hi lo : UInt8) (rest : List UInt8),
    impl.bmpwriter.parseWidth (b0 :: b1 :: b2 :: hi :: lo :: rest)
      = some (hi.toNat * 256 + lo.toNat)

/-- Height decode: on any byte list whose bytes 5 and 6 are present,
    `parseHeight` returns `byte₅·256 + byte₆`. The height companion of
    `spec_parse_width_decode`. -/
def spec_parse_height_decode (impl : RepoImpl) : Prop :=
  ∀ (b0 b1 b2 b3 b4 hi lo : UInt8) (rest : List UInt8),
    impl.bmpwriter.parseHeight (b0 :: b1 :: b2 :: b3 :: b4 :: hi :: lo :: rest)
      = some (hi.toNat * 256 + lo.toNat)

/-- `parseWidth` reports `none` on a list too short to hold a width field (it
    needs bytes 3 and 4, so any list of length `< 5`). Pins the truncation
    failure of the width decode. -/
def spec_parse_width_short (impl : RepoImpl) : Prop :=
  ∀ (bytes : List UInt8),
    bytes.length < 5 → impl.bmpwriter.parseWidth bytes = none

/-- `parseHeight` reports `none` on a list too short to hold a height field (it
    needs bytes 5 and 6, so any list of length `< 7`). Pins the truncation
    failure of the height decode. -/
def spec_parse_height_short (impl : RepoImpl) : Prop :=
  ∀ (bytes : List UInt8),
    bytes.length < 7 → impl.bmpwriter.parseHeight bytes = none

-- ════════════════════════════════════════════════════════════════
-- parse: magic validation, field extraction, rejection
-- ════════════════════════════════════════════════════════════════

/-- Magic rejection: a byte list whose three-byte prefix is not the magic
    `[82,71,66]` is rejected — `parse` returns `none`. -/
def spec_parse_rejects_bad_magic (impl : RepoImpl) : Prop :=
  ∀ (bytes : List UInt8),
    bytes.take 3 ≠ [82, 71, 66] → impl.bmpwriter.parse bytes = none

/-- A truncated header (length `< 7`, too short to hold the seven header bytes)
    is rejected — `parse` returns `none`. Pins the header-length floor: there is
    no field extraction without a complete seven-byte header. -/
def spec_parse_rejects_short (impl : RepoImpl) : Prop :=
  ∀ (bytes : List UInt8),
    bytes.length < 7 → impl.bmpwriter.parse bytes = none

/-- Field extraction on a well-formed header: when the magic is right and the
    header is complete, `parse` recovers the three fields — the width
    `b₃·256 + b₄`, the height `b₅·256 + b₆`, and the payload `drop 7`. -/
def spec_parse_field_extraction (impl : RepoImpl) : Prop :=
  ∀ (wHi wLo hHi hLo : UInt8) (rest : List UInt8),
    impl.bmpwriter.parse (82 :: 71 :: 66 :: wHi :: wLo :: hHi :: hLo :: rest)
      = some (wHi.toNat * 256 + wLo.toNat, hHi.toNat * 256 + hLo.toNat, rest)

/-- `parse`'s recovered width agrees with the independent `parseWidth` decode:
    on a successfully parsed list, the width field equals `parseWidth bytes`.
    Ties the two parse APIs together through the *same* independent decode,
    without going through `build`. -/
def spec_parse_width_consistent (impl : RepoImpl) : Prop :=
  ∀ (wHi wLo hHi hLo : UInt8) (rest : List UInt8),
    (impl.bmpwriter.parse (82 :: 71 :: 66 :: wHi :: wLo :: hHi :: hLo :: rest)).map
        (fun t => t.1)
      = impl.bmpwriter.parseWidth (82 :: 71 :: 66 :: wHi :: wLo :: hHi :: hLo :: rest)

/-- `parse`'s recovered height agrees with the independent `parseHeight`
    decode: on a successfully parsed list, the height field equals
    `parseHeight bytes`. The height companion of `spec_parse_width_consistent`. -/
def spec_parse_height_consistent (impl : RepoImpl) : Prop :=
  ∀ (wHi wLo hHi hLo : UInt8) (rest : List UInt8),
    (impl.bmpwriter.parse (82 :: 71 :: 66 :: wHi :: wLo :: hHi :: hLo :: rest)).map
        (fun t => t.2.1)
      = impl.bmpwriter.parseHeight (82 :: 71 :: 66 :: wHi :: wLo :: hHi :: hLo :: rest)

-- ════════════════════════════════════════════════════════════════
-- validMagic: derived observer
-- ════════════════════════════════════════════════════════════════

/-- `validMagic` is exactly the three-byte-prefix check: `validMagic bytes` is
    `true` iff `bytes.take 3 = [82,71,66]`. Pins the observer to the frozen
    magic tag. -/
def spec_valid_magic_iff (impl : RepoImpl) : Prop :=
  ∀ (bytes : List UInt8),
    impl.bmpwriter.validMagic bytes = true ↔ bytes.take 3 = [82, 71, 66]

/-- Every serialized form passes the magic check: `validMagic (build w h px)` is
    always `true`. Ties the writer to the observer — what `build` emits, the
    magic check accepts. -/
def spec_build_valid_magic (impl : RepoImpl) : Prop :=
  ∀ (w h : Nat) (px : List UInt8),
    impl.bmpwriter.validMagic (impl.bmpwriter.build w h px) = true

/-- `parse` accepts exactly the byte lists that have a complete header (length
    `≥ 7`) and pass the magic check — `parse bytes` is `some _` iff
    `validMagic bytes = true ∧ 7 ≤ bytes.length`. Pins the success domain of
    `parse` to the magic-and-length gate, with no hidden acceptance or
    rejection. -/
def spec_parse_isSome_iff (impl : RepoImpl) : Prop :=
  ∀ (bytes : List UInt8),
    (impl.bmpwriter.parse bytes).isSome = true
      ↔ (impl.bmpwriter.validMagic bytes = true ∧ 7 ≤ bytes.length)

-- ════════════════════════════════════════════════════════════════
-- Round-trip
-- ════════════════════════════════════════════════════════════════

/-- Round-trip: parsing a freshly built image recovers the payload and the
    round-tripped dimensions `(w/256)·256 + w%256` and `(h/256)·256 + h%256`
    (stated on the round-tripped values so it holds for all `w`, `h`). -/
def spec_parse_build_roundtrip (impl : RepoImpl) : Prop :=
  ∀ (w h : Nat) (px : List UInt8),
    impl.bmpwriter.parse (impl.bmpwriter.build w h px)
      = some ((w / 256).toUInt8.toNat * 256 + (w % 256).toUInt8.toNat,
              (h / 256).toUInt8.toNat * 256 + (h % 256).toUInt8.toNat, px)

/-- Round-trip dimensions are exact in range: when `w` and `h` are both below
    `65536`, parsing a built image recovers the *original* `w` and `h` exactly,
    along with the payload. The in-range specialization of
    `spec_parse_build_roundtrip`. -/
def spec_parse_build_roundtrip_inrange (impl : RepoImpl) : Prop :=
  ∀ (w h : Nat) (px : List UInt8),
    w < 65536 → h < 65536 →
      impl.bmpwriter.parse (impl.bmpwriter.build w h px) = some (w, h, px)

-- ════════════════════════════════════════════════════════════════
-- Structural laws over the whole serialize / parse relation.
--
-- These are stated as facts about the writer and the parser as a pair (and
-- about the parser on its full input domain), over arbitrary `w`/`h` and
-- arbitrary byte lists.
-- ════════════════════════════════════════════════════════════════

/-- Distinct in-range inputs serialize to distinct byte lists: if two builds
    agree byte-for-byte, then their widths agree, their heights agree, and their
    payloads agree — provided both dimensions are below `65536` (so they fit the
    16-bit fields). The writer is one-to-one on the in-range domain: the
    serialized form carries enough information to tell two distinct images apart.
    An impl that collapsed two different widths (or heights, or payloads) onto
    the same bytes would violate this. -/
def spec_build_injective (impl : RepoImpl) : Prop :=
  ∀ (w1 h1 : Nat) (px1 : List UInt8) (w2 h2 : Nat) (px2 : List UInt8),
    w1 < 65536 → h1 < 65536 → w2 < 65536 → h2 < 65536 →
      impl.bmpwriter.build w1 h1 px1 = impl.bmpwriter.build w2 h2 px2 →
        w1 = w2 ∧ h1 = h2 ∧ px1 = px2

/-- Parse is a left inverse of build on its own success domain: whenever
    `parse bytes` succeeds with fields `(w, h, pl)`, re-serializing those fields
    reproduces the original input exactly — `build w h pl = bytes`. Any byte
    list the parser accepts is recovered verbatim by the writer from the fields
    the parser reported. An impl whose parser dropped, reordered, or
    misattributed header information so that the writer could not reconstruct the
    input would violate this. -/
def spec_parse_build_left_inverse (impl : RepoImpl) : Prop :=
  ∀ (bytes : List UInt8) (w h : Nat) (pl : List UInt8),
    impl.bmpwriter.parse bytes = some (w, h, pl) →
      impl.bmpwriter.build w h pl = bytes

/-- The recovered payload is the input past the 7-byte header: whenever
    `parse bytes` succeeds with payload `pl`, that payload equals `bytes.drop 7`.
    The third component the parser returns is always the tail of the *input*
    beginning at offset 7 — the frozen header occupies bytes `0…6` and the
    payload is everything after. Anchored on the frozen `drop 7`. An impl that
    started the payload at a different offset, or copied bytes from elsewhere,
    would violate this. -/
def spec_parse_payload_drop7 (impl : RepoImpl) : Prop :=
  ∀ (bytes : List UInt8) (w h : Nat) (pl : List UInt8),
    impl.bmpwriter.parse bytes = some (w, h, pl) →
      pl = bytes.drop 7

/-- On every input the parser either rejects or succeeds-with-a-witnessed-gate:
    for all `bytes`, `parse bytes` is `none`, or it is `some (w, h, pl)` *and*
    the magic check passes *and* the input is at least seven bytes long. There is
    no third outcome — every accepted input carries both a valid magic and a
    complete header, and every other input is rejected. Pins the parser's
    behaviour across its whole domain (including truncated and bad-magic inputs).
    An impl that accepted an input without a valid magic or a full header would
    violate this. -/
def spec_parse_total_dichotomy (impl : RepoImpl) : Prop :=
  ∀ (bytes : List UInt8),
    impl.bmpwriter.parse bytes = none ∨
      (∃ w h pl, impl.bmpwriter.parse bytes = some (w, h, pl)
        ∧ impl.bmpwriter.validMagic bytes = true ∧ 7 ≤ bytes.length)

/-- Every accepted input begins with the magic: whenever `parse bytes` succeeds,
    `bytes.take 3 = [82, 71, 66]`. Acceptance entails the frozen leading tag —
    there is no accepted byte list whose three-byte prefix is anything other than
    the magic. Anchored on the frozen magic `[82,71,66]` and `take 3`. -/
def spec_parse_magic_on_success (impl : RepoImpl) : Prop :=
  ∀ (bytes : List UInt8) (r : Nat × Nat × List UInt8),
    impl.bmpwriter.parse bytes = some r →
      bytes.take 3 = [82, 71, 66]

/-- On any accepted input the width field agrees with the independent
    `parseWidth` decode of the *same* bytes: whenever `parse bytes` succeeds with
    width `w`, `parseWidth bytes = some w`. The two parse APIs report the same
    width on the whole success domain — stated over an *arbitrary* accepted byte
    list, not a fixed header prefix. An impl whose `parse` and `parseWidth`
    disagreed on some accepted input would violate this. -/
def spec_parse_width_on_success (impl : RepoImpl) : Prop :=
  ∀ (bytes : List UInt8) (w h : Nat) (pl : List UInt8),
    impl.bmpwriter.parse bytes = some (w, h, pl) →
      impl.bmpwriter.parseWidth bytes = some w

/-- On any accepted input the height field agrees with the independent
    `parseHeight` decode of the *same* bytes: whenever `parse bytes` succeeds
    with height `h`, `parseHeight bytes = some h`. The height companion of
    `spec_parse_width_on_success`, over an arbitrary accepted byte list. -/
def spec_parse_height_on_success (impl : RepoImpl) : Prop :=
  ∀ (bytes : List UInt8) (w h : Nat) (pl : List UInt8),
    impl.bmpwriter.parse bytes = some (w, h, pl) →
      impl.bmpwriter.parseHeight bytes = some h

/-- Accepted inputs satisfy the header/payload length law: whenever `parse bytes`
    succeeds with payload `pl`, the input length is `7 + pl.length`. The seven
    header bytes plus the payload account for the entire input, with nothing
    dropped or added. An impl that returned a payload longer or shorter than the
    bytes past the header would violate this. -/
def spec_parse_length_law (impl : RepoImpl) : Prop :=
  ∀ (bytes : List UInt8) (w h : Nat) (pl : List UInt8),
    impl.bmpwriter.parse bytes = some (w, h, pl) →
      bytes.length = 7 + pl.length

-- ════════════════════════════════════════════════════════════════
-- Whole-relation laws over arbitrary byte lists.
--
-- These describe the serialize / parse relation as a whole — statements about
-- the writer and parser as a pair.
-- ════════════════════════════════════════════════════════════════

/-- Header observations depend only on the first seven bytes (observational
    determinism): any two byte lists that agree on their leading seven bytes
    (`take 7`) decode to the same width, the same height, and the same magic
    verdict. The three header-derived observations are functions of the
    seven-byte header alone — the payload, the total length, and every byte past
    offset 6 are irrelevant to them. An impl whose width/height/magic reading
    peeked past the seventh byte would violate this. -/
def spec_parse_prefix_determines (impl : RepoImpl) : Prop :=
  ∀ (a b : List UInt8),
    a.take 7 = b.take 7 →
      impl.bmpwriter.parseWidth a = impl.bmpwriter.parseWidth b
      ∧ impl.bmpwriter.parseHeight a = impl.bmpwriter.parseHeight b
      ∧ impl.bmpwriter.validMagic a = impl.bmpwriter.validMagic b

/-- Trailing-byte obliviousness (streaming law): appending arbitrary bytes to a
    parseable input leaves the decoded width and height untouched and simply
    extends the recovered payload by exactly the appended bytes. Whenever
    `parse bytes = some (w, h, pl)`, for every `extra` we have
    `parse (bytes ++ extra) = some (w, h, pl ++ extra)`. The header lives entirely
    in the first seven bytes, so growing the tail can only grow the payload; the
    fields are fixed once the header is present. An impl that let trailing bytes
    perturb the width, the height, or the magic verdict — or that dropped/kept a
    wrong slice of the tail as payload — would violate this. -/
def spec_parse_append_payload (impl : RepoImpl) : Prop :=
  ∀ (bytes : List UInt8) (w h : Nat) (pl : List UInt8),
    impl.bmpwriter.parse bytes = some (w, h, pl) →
      ∀ (extra : List UInt8),
        impl.bmpwriter.parse (bytes ++ extra) = some (w, h, pl ++ extra)

/-- Exact success characterization: `parse` accepts a byte list with fields
    `(w, h, pl)` **iff** both dimensions fit in the 16-bit fields (`< 65536`)
    and the list is exactly the image `build w h pl` builds for those fields.
    Parse and build are inverse on precisely the well-formed, in-range images. -/
def spec_parse_iff_build (impl : RepoImpl) : Prop :=
  ∀ (bytes : List UInt8) (w h : Nat) (pl : List UInt8),
    impl.bmpwriter.parse bytes = some (w, h, pl)
      ↔ (w < 65536 ∧ h < 65536 ∧ impl.bmpwriter.build w h pl = bytes)

/-- The decoded width always fits in 16 bits (codomain law): on any byte list,
    whenever `parseWidth` succeeds, the value it returns is below `65536`. The
    width is recombined from two individual bytes (`hi·256 + lo` with
    `hi, lo < 256`), so it can never exceed the 16-bit range — stated over an
    *arbitrary* byte list, not a fixed header. An impl that read a wider field, or
    combined more than two bytes, could report an out-of-range width and violate
    this. -/
def spec_parse_width_range (impl : RepoImpl) : Prop :=
  ∀ (bytes : List UInt8) (w : Nat),
    impl.bmpwriter.parseWidth bytes = some w → w < 65536

/-- The decoded height always fits in 16 bits (codomain law): the height
    companion of `spec_parse_width_range` — whenever `parseHeight bytes = some h`,
    then `h < 65536`, on an arbitrary byte list. -/
def spec_parse_height_range (impl : RepoImpl) : Prop :=
  ∀ (bytes : List UInt8) (h : Nat),
    impl.bmpwriter.parseHeight bytes = some h → h < 65536

-- ════════════════════════════════════════════════════════════════
-- Byte-frequency and positional laws over the serialized form.
--
-- These describe the serialized byte list not by its exact layout but by
-- aggregate observations — per-byte frequency (`List.count`), first-occurrence
-- position (`List.findIdx?`), and multiset/order identity of the leading tag —
-- over arbitrary `w`/`h` and arbitrary payloads.
-- ════════════════════════════════════════════════════════════════

/-- Frequency invariance under serialization: a byte value `b` occurs exactly as
    often in the serialized image as it does in the raw payload **iff** the
    seven-byte header contributes no copy of `b`. Serializing an image can only
    change a byte's frequency by the amount the fixed header adds; a byte the
    header never emits keeps its payload frequency, and any byte the header does
    emit sees its frequency strictly rise. Stated for every byte value `b` and
    all `w`, `h`, and payloads. An impl that padded, reordered, or duplicated
    payload bytes — or emitted a header of a different composition — would
    violate this. -/
def spec_build_count_unchanged_iff_header_absent (impl : RepoImpl) : Prop :=
  ∀ (w h : Nat) (px : List UInt8) (b : UInt8),
    (impl.bmpwriter.build w h px).count b = px.count b ↔
      ([82, 71, 66, (w / 256).toUInt8, (w % 256).toUInt8,
        (h / 256).toUInt8, (h % 256).toUInt8] : List UInt8).count b = 0

/-- First-occurrence shift for a header-absent byte: if a byte value `b` never
    appears among the seven header bytes, then the first position at which `b`
    occurs in the serialized image is exactly seven greater than its first
    position in the payload. Whenever the header emits no `b` and `b` first
    occurs at payload index `j`, `b` first occurs at serialized index `7 + j`.
    The fixed-width header cannot host the first occurrence of such a byte, so
    the whole payload's first-occurrence index is displaced by the header width
    and by nothing else. An impl that emitted a header of a different width, or
    that let a header byte shadow the payload's first occurrence, would violate
    this. -/
def spec_build_payload_first_index_shift (impl : RepoImpl) : Prop :=
  ∀ (w h : Nat) (px : List UInt8) (b : UInt8) (j : Nat),
    ([82, 71, 66, (w / 256).toUInt8, (w % 256).toUInt8,
      (h / 256).toUInt8, (h % 256).toUInt8] : List UInt8).count b = 0 →
    px.findIdx? (fun x => x == b) = some j →
      (impl.bmpwriter.build w h px).findIdx? (fun x => x == b) = some (7 + j)

/-- Parse determines its input: two byte lists that `parse` accepts with the
    *same* reported triple `(w, h, payload)` are the *same* byte list. Acceptance
    with a given field triple pins the entire input, not merely the recovered
    fields — there is no accepted byte list that reports a triple some other
    accepted byte list also reports. An impl whose parser discarded, or failed to
    faithfully witness, any part of the input it accepted (so two distinct inputs
    could collapse onto one triple) would violate this. -/
def spec_parse_success_injective (impl : RepoImpl) : Prop :=
  ∀ (a b : List UInt8) (r : Nat × Nat × List UInt8),
    impl.bmpwriter.parse a = some r →
    impl.bmpwriter.parse b = some r →
      a = b

/-- Byte-frequency accounting on acceptance: whenever `parse bytes` succeeds with
    fields `(w, h, pl)`, the frequency of every byte value `b` in the accepted
    input splits exactly into the header contribution for `(w, h)` plus the
    payload frequency — `bytes.count b = header(w,h).count b + pl.count b`, for
    every `b`. Every byte of an accepted input is accounted for by the reported
    header fields and the reported payload, with none dropped, added, or
    double-counted. An impl whose parser reported fields inconsistent with the
    bytes it consumed would violate this. -/
def spec_parse_success_count_byte (impl : RepoImpl) : Prop :=
  ∀ (bytes : List UInt8) (w h : Nat) (pl : List UInt8) (b : UInt8),
    impl.bmpwriter.parse bytes = some (w, h, pl) →
      bytes.count b =
        ([82, 71, 66, (w / 256).toUInt8, (w % 256).toUInt8,
          (h / 256).toUInt8, (h % 256).toUInt8] : List UInt8).count b
        + pl.count b

/-- Ordered-multiset recovery of the leading tag: among all length-three byte
    lists with no repeats whose bytes strictly *descend* by numeric value, the
    one whose per-byte frequencies match the serialized image's three-byte prefix
    is that prefix itself. Frequencies alone fix only the *set* of bytes; adding
    the no-repeat and strict-descending-order constraints pins the *sequence*
    uniquely, and it coincides with the frozen magic prefix. An impl emitting a
    different leading tag, or one whose prefix bytes were not a strictly
    descending triple, would fail to satisfy this recovery. -/
def spec_build_magic_prefix_unique_counts (impl : RepoImpl) : Prop :=
  ∀ (w h : Nat) (px pref : List UInt8),
    pref.length = 3 →
    pref.Nodup →
    pref.Pairwise (fun a b => b.toNat < a.toNat) →
    (∀ b : UInt8, pref.count b = ((impl.bmpwriter.build w h px).take 3).count b) →
      pref = (impl.bmpwriter.build w h px).take 3

-- ════════════════════════════════════════════════════════════════
-- Bit-level decode bridges and modular field laws.
--
-- These pin the header fields through a decode that is stated with bit
-- operations (`<<<`, `|||`, `>>>`, `&&&`) or a modular characterization
-- rather than the `hi·256 + lo` / `w/256, w%256` forms the writer emits —
-- the same 16-bit big-endian field, read a different-but-equal way.
-- ════════════════════════════════════════════════════════════════

/-- Bitwise width decode: on any byte list whose bytes 3 and 4 are present,
    `parseWidth` returns the 16-bit big-endian value assembled by placing the
    high byte in the top eight bits and the low byte in the bottom eight —
    `(hi.toNat <<< 8) ||| lo.toNat`. The width field read through a
    shift-and-or, on an arbitrary list. -/
def spec_parse_width_bitwise_decode (impl : RepoImpl) : Prop :=
  ∀ (bytes : List UInt8) (hi lo : UInt8),
    bytes[3]? = some hi → bytes[4]? = some lo →
      impl.bmpwriter.parseWidth bytes = some ((hi.toNat <<< 8) ||| lo.toNat)

/-- Bitwise height decode: the height companion of
    `spec_parse_width_bitwise_decode` — on any list whose bytes 5 and 6 are
    present, `parseHeight` returns `(hi.toNat <<< 8) ||| lo.toNat`. -/
def spec_parse_height_bitwise_decode (impl : RepoImpl) : Prop :=
  ∀ (bytes : List UInt8) (hi lo : UInt8),
    bytes[5]? = some hi → bytes[6]? = some lo →
      impl.bmpwriter.parseHeight bytes = some ((hi.toNat <<< 8) ||| lo.toNat)

/-- Low-16 round-trip: parsing a freshly built image recovers, for the two
    dimensions, exactly their low sixteen bits — `w &&& 65535` and
    `h &&& 65535` — together with the payload verbatim. The 16-bit fields store
    each dimension modulo `65536`, expressed here as a bit-mask. -/
def spec_parse_build_roundtrip_low16_mask (impl : RepoImpl) : Prop :=
  ∀ (w h : Nat) (px : List UInt8),
    impl.bmpwriter.parse (impl.bmpwriter.build w h px)
      = some (w &&& 65535, h &&& 65535, px)

/-- Indexed dimension bytes: for each of the two positions `i < 2`, the width
    byte at serialized offset `3 + i` and the height byte at offset `5 + i` are
    the corresponding big-endian octet of the dimension — the byte obtained by
    shifting down `8·(1 - i)` bits and masking to eight bits. Positional reads of
    the header dimension octets, at computed offsets, through shift-and-mask. -/
def spec_build_dimension_field_indexed_mask (impl : RepoImpl) : Prop :=
  ∀ (w h : Nat) (px : List UInt8) (i : Nat),
    i < 2 →
      (impl.bmpwriter.build w h px)[3 + i]?
          = some (((w >>> (8 * (1 - i))) &&& 255).toUInt8)
      ∧ (impl.bmpwriter.build w h px)[5 + i]?
          = some (((h >>> (8 * (1 - i))) &&& 255).toUInt8)

/-- Algebraic characterization of the magic prefix: `validMagic bytes` holds iff
    the first three bytes exist and their `Nat` values `(a, b, c)` are the
    strictly-descending triple with elementary-symmetric fingerprint `a+b+c =
    219`, `ab+ac+bc = 15920`, `abc = 384252`. Those symmetric sums together with
    the descending order pin the sequence to the frozen magic `[82, 71, 66]`. -/
def spec_valid_magic_algebraic_prefix (impl : RepoImpl) : Prop :=
  ∀ (bytes : List UInt8),
    impl.bmpwriter.validMagic bytes = true ↔
      ∃ (a b c : UInt8),
        bytes[0]? = some a ∧ bytes[1]? = some b ∧ bytes[2]? = some c ∧
        a.toNat + b.toNat + c.toNat = 219 ∧
        a.toNat * b.toNat + a.toNat * c.toNat + b.toNat * c.toNat = 15920 ∧
        a.toNat * b.toNat * c.toNat = 384252 ∧
        b.toNat < a.toNat ∧ c.toNat < b.toNat

-- ════════════════════════════════════════════════════════════════
-- Per-component build injectivity.
--
-- Each of the three arguments is separately faithful in the serialized form,
-- holding the other two fixed (dimensions on their in-range domain).
-- ════════════════════════════════════════════════════════════════

/-- Width faithfulness: with the height and payload held fixed, two in-range
    widths that serialize to the same byte list are equal — the width field
    carries the full 16-bit width when it fits. -/
def spec_build_width_injective_fixed_height_payload (impl : RepoImpl) : Prop :=
  ∀ (w1 w2 h : Nat) (px : List UInt8),
    w1 < 65536 → w2 < 65536 →
      impl.bmpwriter.build w1 h px = impl.bmpwriter.build w2 h px → w1 = w2

/-- Height faithfulness: with the width and payload held fixed, two in-range
    heights that serialize to the same byte list are equal — the height
    companion of `spec_build_width_injective_fixed_height_payload`. -/
def spec_build_height_injective_fixed_width_payload (impl : RepoImpl) : Prop :=
  ∀ (h1 h2 w : Nat) (px : List UInt8),
    h1 < 65536 → h2 < 65536 →
      impl.bmpwriter.build w h1 px = impl.bmpwriter.build w h2 px → h1 = h2

/-- Payload faithfulness: with both dimensions held fixed, two payloads that
    serialize to the same byte list are equal — the appended payload is carried
    verbatim with nothing dropped, padded, or shared with the header. -/
def spec_build_payload_injective_fixed_dimensions (impl : RepoImpl) : Prop :=
  ∀ (w h : Nat) (px1 px2 : List UInt8),
    impl.bmpwriter.build w h px1 = impl.bmpwriter.build w h px2 → px1 = px2

/-- Width-byte checksum agreement: for an in-range width, the two serialized
    width bytes `hi`, `lo` at offsets 3 and 4 recombine to the decoded width
    `hi·256 + lo`, and their byte-sum `hi + lo` equals the sum of the two
    arithmetic components `w/256 + w%256` of the original width. -/
def spec_width_header_checksum_matches_decode (impl : RepoImpl) : Prop :=
  ∀ (w h : Nat) (px : List UInt8),
    w < 65536 →
      match (impl.bmpwriter.build w h px)[3]?,
            (impl.bmpwriter.build w h px)[4]?,
            impl.bmpwriter.parseWidth (impl.bmpwriter.build w h px) with
      | some hi, some lo, some decoded =>
          decoded = hi.toNat * 256 + lo.toNat ∧
            hi.toNat + lo.toNat = w / 256 + w % 256
      | _, _, _ => False
