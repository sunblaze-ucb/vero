/-!
# VestV2.Impl.BufTraits

Buffer trait type classes for the VestV2 parser/serializer framework.
These type classes define the interface for input and output buffers.
Types are fixed vocabulary (DO NOT MODIFY).
-/

-- ── Core type classes (DO NOT MODIFY) ───────────────────────

/-- Trait for types that can be used as input for VestV2 parsers.
    Roughly corresponds to byte buffers. Does not expose contents,
    so opaque buffer types for side-channel security can implement it. -/
class VestInput (α : Type) where
  length : α → Nat
  subrange : α → Nat → Nat → α
  clone : α → α

/-- Trait for public input buffers that expose their contents as bytes. -/
class VestPublicInput (α : Type) extends VestInput α where
  as_byte_slice : α → List UInt8

/-- Trait for types that can be used as output for VestV2 serializers.
    Does not expose contents, so opaque buffer types for side-channel
    security can implement it. -/
class VestOutput (α : Type) (I : outParam Type) where
  length : α → Nat
  set_range : α → Nat → I → α

/-- Trait for public output buffers that can be set using transparent bytes. -/
class VestPublicOutput (α : Type) (I : outParam Type) extends VestOutput α I where
  set_byte : α → Nat → UInt8 → α
