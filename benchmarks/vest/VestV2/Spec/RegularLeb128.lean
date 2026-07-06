import VestV2.Impl.RegularLeb128
import VestV2.Harness

/-!
# VestV2.Spec.RegularLeb128

Specifications for the LEB128 module. Each `spec_*` is a property
over an arbitrary `impl : RepoImpl`.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- LEB128 spec_parse only yields values that fit in u64. -/
def spec_leb128_value_fits (_impl : RepoImpl) : Prop :=
  ∀ (s : List UInt8) (n : Int) (v : UInt),
  Leb128.spec_parse s = some (n, v) → leb128Fits v = true

/-- LEB128 satisfies the serialize-then-parse roundtrip for any n < 2^64. -/
def spec_leb128_roundtrip (_impl : RepoImpl) : Prop :=
  ∀ (n : UInt), leb128Fits n = true →
  ∃ (len : Int), len > 0 ∧ Leb128.spec_parse (Leb128.spec_serialize n) = some (len, n)

/-- If LEB128 spec_parse succeeds, serializing the parsed value gives
    back the consumed prefix. -/
def spec_leb128_parse_serialize_roundtrip (_impl : RepoImpl) : Prop :=
  ∀ (s : List UInt8) (n : Int) (v : UInt),
  Leb128.spec_parse s = some (n, v) →
  Leb128.spec_serialize v = s.take n.toNat

/-- The exec leb128Parse agrees with the spec on both success and failure. -/
def spec_leb128_parse_correct (impl : RepoImpl) : Prop :=
  ∀ (s : List UInt8),
    (∀ (n : Int) (v : UInt),
      Leb128.spec_parse s = some (n, v) → impl.vest.leb128Parse s = Except.ok (n.toNat, v)) ∧
    (Leb128.spec_parse s = none → ∃ e, impl.vest.leb128Parse s = Except.error e)
