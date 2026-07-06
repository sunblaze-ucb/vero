import Eth20Dafny.Harness

/-!
# Eth20Dafny.Spec.SszBoolSeDes

Specifications for boolean serialization and deserialization.

The specs below are source-backed by the postconditions and preconditions in
`ssz/BoolSeDes.dfy`.
-/

def spec_boolToBytes_length (impl : RepoImpl) : Prop :=
  ∀ (b : Bool), (impl.eth2Dafny.boolToBytes b).length = 1

def spec_boolToBytes_value (impl : RepoImpl) : Prop :=
  ∀ (b : Bool), impl.eth2Dafny.boolToBytes b = [impl.eth2Dafny.boolToByte b]

def spec_boolSeDesByteToBool_canonical (impl : RepoImpl) : Prop :=
  ∀ (b : UInt8), b.toNat ≤ 1 →
    impl.eth2Dafny.boolSeDesByteToBool [b] = impl.eth2Dafny.bytesAndBitsByteToBool b

def spec_boolSeDes_roundtrip (impl : RepoImpl) : Prop :=
  ∀ (b : Bool), impl.eth2Dafny.boolSeDesByteToBool (impl.eth2Dafny.boolToBytes b) = b
