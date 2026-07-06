import Eth20Dafny.Harness

/-!
# Eth20Dafny.Spec.SszBitVectorSeDes

Specifications for SSZ bitvector serialization and deserialization. Each
`spec_*` is a property over an arbitrary `impl : RepoImpl`.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- Source-backed Dafny specification `BitVectorSeDes.bitvectorDecodeEncodeIsIdentity`. -/
def spec_bitvectorDecodeEncodeIsIdentity (impl : RepoImpl) : Prop :=
  ∀ (l : List Bool), 0 < l.length → impl.eth2Dafny.fromBytesToBitVector (impl.eth2Dafny.fromBitvectorToBytes l) l.length = l

/-- Source-backed Dafny specification `BitVectorSeDes.bitvectorEncodeDecodeIsIdentity`. -/
def spec_bitvectorEncodeDecodeIsIdentity (impl : RepoImpl) : Prop :=
  ∀ (xb : List UInt8) (len : Nat), Eth20Dafny.isValidBitVectorEncoding xb len → impl.eth2Dafny.fromBitvectorToBytes (impl.eth2Dafny.fromBytesToBitVector xb len) = xb

/-- Source-backed Dafny specification `BitVectorSeDes.bitvectorSerialiseIsInjectiveGeneral`. -/
def spec_bitvectorSerialiseIsInjectiveGeneral (impl : RepoImpl) : Prop :=
  ∀ (l1 : List Bool) (l2 : List Bool), l1.length = l2.length → 0 < l1.length → impl.eth2Dafny.fromBitvectorToBytes l1 = impl.eth2Dafny.fromBitvectorToBytes l2 → l1 = l2

/-- Source-backed Dafny specification `BitVectorSeDes.bitvectorDeserialiseIsInjective`. -/
def spec_bitvectorDeserialiseIsInjective (impl : RepoImpl) : Prop :=
  ∀ (xa : List UInt8) (xb : List UInt8) (lena : Nat) (lenb : Nat), Eth20Dafny.isValidBitVectorEncoding xa lena → Eth20Dafny.isValidBitVectorEncoding xb lenb → impl.eth2Dafny.fromBytesToBitVector xa lena = impl.eth2Dafny.fromBytesToBitVector xb lenb → xa = xb
