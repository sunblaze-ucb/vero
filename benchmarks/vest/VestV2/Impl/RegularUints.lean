/-!
# VestV2.Impl.RegularUints

Combinator types for parsing and serializing unsigned integers (u8, u16,
u32, u64) in both little-endian and big-endian byte order, plus a 24-bit
unsigned integer type (u24). Also defines the `FromToBytes` type class
for byte conversion.

Types and spec helpers are fixed vocabulary (DO NOT MODIFY).
-/

-- ── Types (DO NOT MODIFY) ─────────────────────────────────

/-- Combinator for parsing and serializing unsigned u8 integers. -/
structure U8 where
  deriving Inhabited

/-- Combinator for parsing and serializing unsigned u16 integers in little-endian byte order. -/
structure U16Le where
  deriving Inhabited

/-- Combinator for parsing and serializing unsigned u32 integers in little-endian byte order. -/
structure U32Le where
  deriving Inhabited

/-- Combinator for parsing and serializing unsigned u64 integers in little-endian byte order. -/
structure U64Le where
  deriving Inhabited

/-- Combinator for parsing and serializing unsigned u16 integers in big-endian byte order. -/
structure U16Be where
  deriving Inhabited

/-- Combinator for parsing and serializing unsigned u32 integers in big-endian byte order. -/
structure U32Be where
  deriving Inhabited

/-- Combinator for parsing and serializing unsigned u64 integers in big-endian byte order. -/
structure U64Be where
  deriving Inhabited

/-- VestV2's u24: 24-bit unsigned integer, stored as a natural number. -/
abbrev u24 := Nat

/-- Combinator for parsing and serializing unsigned u24 integers in little-endian byte order. -/
structure U24Le where
  deriving Inhabited

/-- Combinator for parsing and serializing unsigned u24 integers in big-endian byte order. -/
structure U24Be where
  deriving Inhabited

/-- Trait for converting an integer type to and from a sequence of bytes. -/
class FromToBytes (α : Type) where
  sizeOf : Nat
  toLe : α → List UInt8
  fromLe : List UInt8 → Option α
  toBe : α → List UInt8
  fromBe : List UInt8 → Option α

-- ── Spec helpers (no markers — fixed vocabulary) ──────────

namespace U8

/-- Specification of parse for U8: reads one byte. -/
def spec_parse (_ : U8) (s : List UInt8) : Option (Int × UInt8) :=
  match s with
  | b :: _ => some (1, b)
  | [] => none

/-- Specification of serialize for U8: writes one byte. -/
def spec_serialize (_ : U8) (v : UInt8) : List UInt8 :=
  [v]

end U8
