-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Bmpwriter.Impl.Image

Serializer/parser for a fixed-width image schema. The operations are `build`
(serialize a width/height/pixel triple to a flat byte list), `parseWidth` /
`parseHeight` (decode the two dimension fields), `parse` (validate the magic and
recover the triple), and `validMagic` (the leading-tag observer).

The schema is a 7-byte header — the three magic bytes `[82, 71, 66]`, then the
width and height each as a 16-bit big-endian pair — followed by the pixel
payload verbatim, with no compression or row padding. Dimensions are `Nat`,
bytes are `UInt8`.

Types and signatures are fixed vocabulary (DO NOT MODIFY). The exact behaviour
each API must satisfy is pinned by `Spec/Image.lean`.
-/

-- ── Core data types (DO NOT MODIFY) ──────────────────────────

/-- The three magic bytes that prefix every serialized image: `[82, 71, 66]`. -/
abbrev magicBytes : List UInt8 := [82, 71, 66]

namespace Bmpwriter

-- ── API signatures (DO NOT MODIFY) ───────────────────────────

/-- `build w h pixels`: serialize a width, height, and pixel payload into the
    flat byte layout — the 7-byte header (`magic ++ width-be ++ height-be`)
    followed by the raw payload. -/
abbrev BuildSig := Nat → Nat → List UInt8 → List UInt8

/-- `parseWidth bytes`: the decoded 16-bit big-endian width — `byte₃·256 +
    byte₄` — or `none` if the byte list is too short to hold a width field. -/
abbrev ParseWidthSig := List UInt8 → Option Nat

/-- `parseHeight bytes`: the decoded 16-bit big-endian height — `byte₅·256 +
    byte₆` — or `none` if the byte list is too short to hold a height field. -/
abbrev ParseHeightSig := List UInt8 → Option Nat

/-- `parse bytes`: validate the magic and recover `(width, height, payload)`,
    or `none` if the magic is wrong or the header is truncated. -/
abbrev ParseSig := List UInt8 → Option (Nat × Nat × List UInt8)

/-- `validMagic bytes`: whether `bytes` begins with the three magic bytes
    `[82, 71, 66]`. -/
abbrev ValidMagicSig := List UInt8 → Bool

end Bmpwriter

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- !benchmark @start code_aux def=build
-- !benchmark @end code_aux def=build

def Bmpwriter.build : Bmpwriter.BuildSig :=
-- !benchmark @start code def=build
  fun w h pixels =>
    [82, 71, 66,
     (w / 256).toUInt8, (w % 256).toUInt8,
     (h / 256).toUInt8, (h % 256).toUInt8] ++ pixels
-- !benchmark @end code def=build

-- !benchmark @start code_aux def=validMagic
-- !benchmark @end code_aux def=validMagic

def Bmpwriter.validMagic : Bmpwriter.ValidMagicSig :=
-- !benchmark @start code def=validMagic
  fun bytes => bytes.take 3 == [82, 71, 66]
-- !benchmark @end code def=validMagic

-- !benchmark @start code_aux def=parseWidth
-- !benchmark @end code_aux def=parseWidth

def Bmpwriter.parseWidth : Bmpwriter.ParseWidthSig :=
-- !benchmark @start code def=parseWidth
  fun bytes =>
    match bytes[3]?, bytes[4]? with
    | some hi, some lo => some (hi.toNat * 256 + lo.toNat)
    | _, _ => none
-- !benchmark @end code def=parseWidth

-- !benchmark @start code_aux def=parseHeight
-- !benchmark @end code_aux def=parseHeight

def Bmpwriter.parseHeight : Bmpwriter.ParseHeightSig :=
-- !benchmark @start code def=parseHeight
  fun bytes =>
    match bytes[5]?, bytes[6]? with
    | some hi, some lo => some (hi.toNat * 256 + lo.toNat)
    | _, _ => none
-- !benchmark @end code def=parseHeight

-- !benchmark @start code_aux def=parse
-- !benchmark @end code_aux def=parse

def Bmpwriter.parse : Bmpwriter.ParseSig :=
-- !benchmark @start code def=parse
  fun bytes =>
    match bytes[3]?, bytes[4]?, bytes[5]?, bytes[6]? with
    | some wHi, some wLo, some hHi, some hLo =>
        if bytes.take 3 == [82, 71, 66] then
          some (wHi.toNat * 256 + wLo.toNat, hHi.toNat * 256 + hLo.toNat, bytes.drop 7)
        else none
    | _, _, _, _ => none
-- !benchmark @end code def=parse
