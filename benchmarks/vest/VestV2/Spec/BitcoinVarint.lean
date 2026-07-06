import VestV2.Impl.BitcoinVarint
import VestV2.Harness

/-!
# VestV2.Spec.BitcoinVarint

Specifications for Bitcoin variable-length integer operations. Each
`spec_*` is a property over an arbitrary `impl : RepoImpl`; theorem
stubs live in `VestV2/Proof/BitcoinVarint.lean`.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- Bitcoin VarInt: values < 0xFD encode as a single byte, and parsing
    that byte yields VarInt.U8 with the original value. -/
def spec_btcvarint_u8_roundtrip (_impl : RepoImpl) : Prop :=
  ∀ (v : UInt8), v.toNat < 0xFD →
    VarInt.spec_parse [v] = some (1, VarInt.U8 v)

/-- When Bitcoin VarInt spec_parse succeeds on buffer s consuming n bytes,
    then 1 ≤ n ≤ 9 ∧ n ≤ s.length. -/
def spec_btcvarint_parse_length_bounds (_impl : RepoImpl) : Prop :=
  ∀ (s : List UInt8) (n : Int) (v : VarInt),
    VarInt.spec_parse s = some (n, v) →
    1 ≤ n ∧ n ≤ 9 ∧ n.toNat ≤ s.length

/-- When VarInt.spec_parse returns a U16 value, it satisfies the fit
    predicate (≥ 0xFD). -/
def spec_btcvarint_u16_range (_impl : RepoImpl) : Prop :=
  ∀ (s : List UInt8) (n : Int) (v : UInt16),
    VarInt.spec_parse s = some (n, VarInt.U16 v) →
    predU16LeFitApply v = true

/-- When VarInt.spec_parse returns a U32 value, it satisfies the fit
    predicate (≥ 0x10000). -/
def spec_btcvarint_u32_range (_impl : RepoImpl) : Prop :=
  ∀ (s : List UInt8) (n : Int) (v : UInt32),
    VarInt.spec_parse s = some (n, VarInt.U32 v) →
    predU32LeFitApply v = true

/-- When VarInt.spec_parse returns a U64 value, it satisfies the fit
    predicate (≥ 0x100000000). -/
def spec_btcvarint_u64_range (_impl : RepoImpl) : Prop :=
  ∀ (s : List UInt8) (n : Int) (v : UInt64),
    VarInt.spec_parse s = some (n, VarInt.U64 v) →
    predU64LeFitApply v = true

/-- btcVarintParse agrees with VarInt.spec_parse on both success and failure. -/
def spec_btcvarint_parse_correct (impl : RepoImpl) : Prop :=
  ∀ (s : List UInt8),
    (∀ (n : Int) (v : VarInt),
      VarInt.spec_parse s = some (n, v) →
      impl.vest.btcVarintParse s = Except.ok (n.toNat, v)) ∧
    (VarInt.spec_parse s = none → ∃ e, impl.vest.btcVarintParse s = Except.error e)

/-- btcVarintSerialize reports the standard compact-size encoding
    length for each constructor whenever the destination buffer is
    large enough, and otherwise returns InsufficientBuffer. -/
def spec_btcvarint_serialize_size_correct (impl : RepoImpl) : Prop :=
  ∀ (v : VarInt) (buf : List UInt8) (pos : Nat),
    let need :=
      match v with
      | VarInt.U8 _ => 1
      | VarInt.U16 _ => 3
      | VarInt.U32 _ => 5
      | VarInt.U64 _ => 9
    (pos + need ≤ buf.length → impl.vest.btcVarintSerialize v buf pos = Except.ok need) ∧
    (buf.length < pos + need →
      impl.vest.btcVarintSerialize v buf pos = Except.error SerializeError.InsufficientBuffer)
