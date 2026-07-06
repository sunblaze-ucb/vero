import Eth20Dafny.Harness

/-!
# Eth20Dafny.Spec.SszBytesAndBits

Specifications and spec helpers for `SszBytesAndBits`.

DO NOT MODIFY — this file is frozen curator-given content.
-/

namespace Eth20Dafny

/-- Source-backed spec helper `BytesAndBits.isNull`. -/
def isNull (l : List Bool) : Prop :=
  ∀ b, b ∈ l → b = false

end Eth20Dafny

/-- Source-backed spec `BytesAndBits.encodeOfDecodeByteIsIdentity`. -/
def spec_encodeOfDecodeByteIsIdentity (impl : RepoImpl) : Prop :=
  ∀ (n : UInt8), impl.eth2Dafny.list8BitsToByte (impl.eth2Dafny.byteTo8Bits n) = n

/-- Helper lemma used inside encodeOfDecodeByteIsIdentity. -/
def spec_lemmaBoolToByteIsTheInverseOfByteToBool (impl : RepoImpl) : Prop :=
  ∀ (b : UInt8), b.toNat ≤ 1 →
    impl.eth2Dafny.boolToByte (impl.eth2Dafny.bytesAndBitsByteToBool b) = b

/-- Source-backed spec `BytesAndBits.decodeOfEncode8BitsIsIdentity`. -/
def spec_decodeOfEncode8BitsIsIdentity (impl : RepoImpl) : Prop :=
  ∀ (l : List Bool), l.length = 8 → impl.eth2Dafny.byteTo8Bits (impl.eth2Dafny.list8BitsToByte l) = l

/-- Source-backed spec `BytesAndBits.byteIsZeroIffBinaryIsNull`. -/
def spec_byteIsZeroIffBinaryIsNull (impl : RepoImpl) : Prop :=
  ∀ (n : UInt8), n = 0 ↔ Eth20Dafny.isNull (impl.eth2Dafny.byteTo8Bits n)

/-- Source-backed postcondition for `BytesAndBits.fromBitsToBytes`: the byte
length is the bit length rounded up to complete bytes. -/
def spec_fromBitsToBytes_length (impl : RepoImpl) : Prop :=
  ∀ (l : List Bool),
    (impl.eth2Dafny.fromBitsToBytes l).length = Eth20Dafny.ceil l.length 8

/-- Source-backed postcondition for `BytesAndBits.fromBitsToBytes`: if the
final source bit is set, then the final encoded byte is nonzero. -/
def spec_fromBitsToBytes_last_nonzero (impl : RepoImpl) : Prop :=
  ∀ (l : List Bool),
    0 < l.length →
    l.getD (l.length - 1) false = true →
    1 ≤ ((impl.eth2Dafny.fromBitsToBytes l).getD ((impl.eth2Dafny.fromBitsToBytes l).length - 1) 0).toNat
