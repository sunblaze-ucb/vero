import Eth20Dafny.Harness

/-!
# Eth20Dafny.Spec.SszBitListSeDes

Specifications for bit list serialization and deserialization.

No scored specs are assigned to this module.
-/

def spec_bitlistDecodeEncodeIsIdentity (impl : RepoImpl) : Prop :=
  ∀ (l : List Bool),
    impl.eth2Dafny.fromBytesToBitList (impl.eth2Dafny.fromBitlistToBytes l) = l

def spec_bitlistEncodeDecodeIsIdentity (impl : RepoImpl) : Prop :=
  ∀ (xb : List UInt8),
    0 < xb.length →
    1 ≤ (xb.getD (xb.length - 1) 0).toNat →
    impl.eth2Dafny.fromBitlistToBytes (impl.eth2Dafny.fromBytesToBitList xb) = xb

def spec_bitlistSerialiseIsInjective (impl : RepoImpl) : Prop :=
  ∀ (l1 : List Bool) (l2 : List Bool),
    impl.eth2Dafny.fromBitlistToBytes l1 = impl.eth2Dafny.fromBitlistToBytes l2 →
    l1 = l2

def spec_bitlistDeserialiseIsInjective (impl : RepoImpl) : Prop :=
  ∀ (xa : List UInt8) (xb : List UInt8),
    0 < xa.length →
    1 ≤ (xa.getD (xa.length - 1) 0).toNat →
    0 < xb.length →
    1 ≤ (xb.getD (xb.length - 1) 0).toNat →
    impl.eth2Dafny.fromBytesToBitList xa = impl.eth2Dafny.fromBytesToBitList xb →
    xa = xb

def spec_simplifyFromByteToListFirstArg (impl : RepoImpl) : Prop :=
  ∀ (b : UInt8) (m : List UInt8),
    0 < m.length →
    1 ≤ (m.getD (m.length - 1) 0).toNat →
    impl.eth2Dafny.fromBytesToBitList (b :: m) = impl.eth2Dafny.byteTo8Bits b ++ impl.eth2Dafny.fromBytesToBitList m

def spec_simplifyFromBitListToByteFirstArg (impl : RepoImpl) : Prop :=
  ∀ (e : UInt8) (xl : List Bool),
    impl.eth2Dafny.fromBitlistToBytes (impl.eth2Dafny.byteTo8Bits e ++ xl) = e :: impl.eth2Dafny.fromBitlistToBytes xl

def spec_surjective (impl : RepoImpl) : Prop :=
  ∀ (xb : List UInt8),
    0 < xb.length →
    1 ≤ (xb.getD (xb.length - 1) 0).toNat →
    ∃ l : List Bool, xb = impl.eth2Dafny.fromBitlistToBytes l

/-- Source-backed postcondition for `BitListSeDes.largestIndexOfOne`: the
returned index is in bounds when the byte-sized list contains a true bit. -/
def spec_largestIndexOfOne_bounds (impl : RepoImpl) : Prop :=
  ∀ (l : List Bool),
    l.length = 8 →
    (∃ b, b ∈ l ∧ b = true) →
    impl.eth2Dafny.largestIndexOfOne l < l.length

/-- Source-backed postcondition for `BitListSeDes.largestIndexOfOne`: the
returned position contains a true bit. -/
def spec_largestIndexOfOne_points_to_true (impl : RepoImpl) : Prop :=
  ∀ (l : List Bool),
    l.length = 8 →
    (∃ b, b ∈ l ∧ b = true) →
    l.getD (impl.eth2Dafny.largestIndexOfOne l) false = true

/-- Source-backed postcondition for `BitListSeDes.largestIndexOfOne`: every
later position is false. -/
def spec_largestIndexOfOne_last_true (impl : RepoImpl) : Prop :=
  ∀ (l : List Bool) (i : Nat),
    l.length = 8 →
    impl.eth2Dafny.largestIndexOfOne l < i →
    i < l.length →
    l.getD i false = false
