import VestV2.Impl.RegularUints
import VestV2.Harness

/-!
# VestV2.Spec.RegularUints

Specifications for unsigned integer combinators. Each `spec_*` is a property
over an arbitrary `impl : RepoImpl`.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- The Lean type-size facts: UInt8 occupies 1 byte, UInt16 2 bytes,
    UInt32 4 bytes, UInt64 8 bytes. -/
def spec_size_of_facts (_impl : RepoImpl) : Prop :=
  UInt8.size = 256 ∧ UInt16.size = 65536 ∧ UInt32.size = 4294967296 ∧ UInt64.size = 18446744073709551616

/-- U8 satisfies the roundtrip: parsing the serialization of any byte value
    returns that byte. -/
def spec_u8_roundtrip (_impl : RepoImpl) : Prop :=
  ∀ (v : UInt8),
  U8.spec_parse U8.mk (U8.spec_serialize U8.mk v) = some (1, v)
