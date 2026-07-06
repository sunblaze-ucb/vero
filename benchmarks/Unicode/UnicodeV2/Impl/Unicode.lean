
/-!
# Unicode.Impl.Unicode

Core types, constants, and vocabulary for Unicode 14.0 (Section 3.8–3.9).

These are foundation definitions — other modules import this file.
Types and definitions are fixed vocabulary (DO NOT MODIFY).
-/

-- ── Constants (DO NOT MODIFY) ────────────────────────────────────────────────

/-- Minimum high-surrogate code point value (U+D800). (Section 3.8 D71) -/
def HIGH_SURROGATE_MIN : Nat := 0xD800

/-- Maximum high-surrogate code point value (U+DBFF). (Section 3.8 D71) -/
def HIGH_SURROGATE_MAX : Nat := 0xDBFF

/-- Minimum low-surrogate code point value (U+DC00). (Section 3.8 D73) -/
def LOW_SURROGATE_MIN : Nat := 0xDC00

/-- Maximum low-surrogate code point value (U+DFFF). (Section 3.8 D73) -/
def LOW_SURROGATE_MAX : Nat := 0xDFFF

/-- The assigned Unicode planes: BMP (0), SMP (1), SIP (2), TIP (3),
    SSPP (14), SPUA-A (15), SPUA-B (16). -/
def ASSIGNED_PLANES : List Nat := [0, 1, 2, 3, 14, 15, 16]

-- ── Types (DO NOT MODIFY) ─────────────────────────────────────────────────────

/-- Any value in the Unicode codespace (U+0000 to U+10FFFF). (Section 3.9 D9-D10) -/
abbrev CodePoint := { i : Nat // i ≤ 0x10FFFF }

/-- Test whether a code point lies in one of the assigned Unicode planes.
    The plane number is the upper 16 bits of the code point value. -/
def isInAssignedPlane (i : CodePoint) : Bool :=
  ASSIGNED_PLANES.contains (i.val / 65536)

/-- A Unicode code point in the range U+D800 to U+DBFF. (Section 3.8 D71) -/
abbrev HighSurrogateCodePoint :=
  { p : CodePoint // HIGH_SURROGATE_MIN ≤ p.val ∧ p.val ≤ HIGH_SURROGATE_MAX }

/-- A Unicode code point in the range U+DC00 to U+DFFF. (Section 3.8 D73) -/
abbrev LowSurrogateCodePoint :=
  { p : CodePoint // LOW_SURROGATE_MIN ≤ p.val ∧ p.val ≤ LOW_SURROGATE_MAX }

/-- Any Unicode code point except high-surrogate and low-surrogate code points.
    (Section 3.9 D76) -/
abbrev ScalarValue :=
  { p : CodePoint //
      (p.val < HIGH_SURROGATE_MIN ∨ p.val > HIGH_SURROGATE_MAX) ∧
      (p.val < LOW_SURROGATE_MIN  ∨ p.val > LOW_SURROGATE_MAX) }

/-- A Unicode code point that belongs to an assigned Unicode plane. -/
abbrev AssignedCodePoint := { p : CodePoint // isInAssignedPlane p = true }

