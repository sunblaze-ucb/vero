import Eth20Dafny.Harness

/-!
# Eth20Dafny.Spec.SszSerialise

Specifications for SSZ serialisation and deserialisation.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- Source-backed Dafny specification `SSZ.wellTypedDoesNotFail`. -/
def spec_wellTypedDoesNotFail (impl : RepoImpl) : Prop :=
  ∀ (s : Eth20Dafny.Serialisable), Eth20Dafny.wellTyped s →
    impl.eth2Dafny.deserialise (impl.eth2Dafny.serialise s) (Eth20Dafny.typeOf s) ≠ Eth20Dafny.Try.Failure

/-- Source-backed Dafny specification `SSZ.seDesInvolutive`. -/
def spec_seDesInvolutive (impl : RepoImpl) : Prop :=
  ∀ (s : Eth20Dafny.Serialisable), Eth20Dafny.wellTyped s →
    impl.eth2Dafny.deserialise (impl.eth2Dafny.serialise s) (Eth20Dafny.typeOf s) = Eth20Dafny.Try.Success s

/-- Source-backed Dafny specification `SSZ.serialiseIsInjective`. -/
def spec_serialiseIsInjective (impl : RepoImpl) : Prop :=
  ∀ (s1 : Eth20Dafny.Serialisable) (s2 : Eth20Dafny.Serialisable),
    Eth20Dafny.typeOf s1 = Eth20Dafny.typeOf s2 →
    impl.eth2Dafny.serialise s1 = impl.eth2Dafny.serialise s2 →
    s1 = s2

/-- Source-backed postcondition for `Serialise.sizeOf`: for basic SSZ values,
`sizeOf` is bounded and agrees with the serialization length. -/
def spec_sizeOf_basic_bounds_and_length (impl : RepoImpl) : Prop :=
  ∀ (s : Eth20Dafny.Serialisable),
    Eth20Dafny.isBasicTipe (Eth20Dafny.typeOf s) →
    1 ≤ impl.eth2Dafny.sizeOf s ∧
      impl.eth2Dafny.sizeOf s ≤ 32 ∧
      impl.eth2Dafny.sizeOf s = (impl.eth2Dafny.serialise s).length

/-- Source-backed behavior of `Serialise.default` on primitive SSZ types. -/
def spec_default_basic_values (impl : RepoImpl) : Prop :=
  impl.eth2Dafny.default Eth20Dafny.Tipe.Bool_ = Eth20Dafny.RawSerialisable.Bool false ∧
  impl.eth2Dafny.default Eth20Dafny.Tipe.Uint8_ = Eth20Dafny.RawSerialisable.Uint8 0 ∧
  impl.eth2Dafny.default Eth20Dafny.Tipe.Uint16_ = Eth20Dafny.RawSerialisable.Uint16 0 ∧
  impl.eth2Dafny.default Eth20Dafny.Tipe.Uint32_ = Eth20Dafny.RawSerialisable.Uint32 0 ∧
  impl.eth2Dafny.default Eth20Dafny.Tipe.Uint64_ = Eth20Dafny.RawSerialisable.Uint64 0 ∧
  impl.eth2Dafny.default Eth20Dafny.Tipe.Uint128_ = Eth20Dafny.RawSerialisable.Uint128 0 ∧
  impl.eth2Dafny.default Eth20Dafny.Tipe.Uint256_ = Eth20Dafny.RawSerialisable.Uint256 0

/-- Source-backed behavior of `Serialise.default` on fixed-size byte and bit
collection types. -/
def spec_default_collection_values (impl : RepoImpl) : Prop :=
  ∀ (n : Nat),
    impl.eth2Dafny.default (Eth20Dafny.Tipe.Bitvector_ n) =
      Eth20Dafny.RawSerialisable.Bitvector (Eth20Dafny.timeSeq false n) ∧
    impl.eth2Dafny.default (Eth20Dafny.Tipe.Bytes_ n) =
      Eth20Dafny.RawSerialisable.Bytes (Eth20Dafny.timeSeq 0 n)

/-- Source-backed postcondition for `Serialise.serialiseSeqOfBasics` on empty
input. -/
def spec_serialiseSeqOfBasics_empty (impl : RepoImpl) : Prop :=
  impl.eth2Dafny.serialiseSeqOfBasics [] = []

/-- Recursive shape of `Serialise.serialiseSeqOfBasics`, matching the Dafny
definition used to establish the length postcondition. -/
def spec_serialiseSeqOfBasics_cons (impl : RepoImpl) : Prop :=
  ∀ (x : Eth20Dafny.Serialisable) (xs : List Eth20Dafny.Serialisable),
    impl.eth2Dafny.serialiseSeqOfBasics (x :: xs) =
      impl.eth2Dafny.serialise x ++ impl.eth2Dafny.serialiseSeqOfBasics xs

/-- Source-backed length postcondition for nonempty homogeneous basic
sequences. -/
def spec_serialiseSeqOfBasics_length (impl : RepoImpl) : Prop :=
  ∀ (x : Eth20Dafny.Serialisable) (xs : List Eth20Dafny.Serialisable),
    Eth20Dafny.isBasicTipe (Eth20Dafny.typeOf x) →
    (∀ y, y ∈ xs → Eth20Dafny.typeOf y = Eth20Dafny.typeOf x) →
    (impl.eth2Dafny.serialiseSeqOfBasics (x :: xs)).length =
      (x :: xs).length * (impl.eth2Dafny.serialise x).length
