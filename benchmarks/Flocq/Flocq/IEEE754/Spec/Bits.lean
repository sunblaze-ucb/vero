import Flocq.Harness
import Flocq.IEEE754.Impl.Bits

open Flocq

/-!
# Flocq.IEEE754.Spec.Bits

Specifications for the bit-pattern encoding/decoding functions defined in
`Impl/IEEE754.Bits.lean`, corresponding to key theorems from
`src/IEEE754/Bits.v`.

The specs cover:
- Round-trip from `BinaryFloat` to bits and back yields the original float
- Round-trip from bits to `BinaryFloat` and back yields the original bit pattern

All specs access API functions via `impl.flocq.*` through `RepoImpl`.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- `validBinary` exposes the shared BinaryFloat validity helper. -/
def spec_validBinary_def (impl : RepoImpl) : Prop :=
  ∀ (mw ew x : Int),
    impl.flocq.validBinary (mw + 1) ((2 : Int) ^ (ew - 1).toNat)
      (impl.flocq.binaryFloatOfBitsAux mw ew x) = true

/-- Binary32 binary-operation NaN propagation agrees with the shared helper. -/
def spec_binopNanPl32_def (impl : RepoImpl) : Prop :=
  ∀ (x y : Binary32),
    impl.flocq.binopNanPl32 x y = BinaryFloat.nan false 1

/-- Binary64 binary-operation NaN propagation agrees with the shared helper. -/
def spec_binopNanPl64_def (impl : RepoImpl) : Prop :=
  ∀ (x y : Binary64),
    impl.flocq.binopNanPl64 x y = BinaryFloat.nan false 1

/-- Binary32 unary-operation NaN propagation agrees with the shared helper. -/
def spec_unopNanPl32_def (impl : RepoImpl) : Prop :=
  ∀ (x : Binary32),
    impl.flocq.unopNanPl32 x = BinaryFloat.nan false 1

/-- Binary64 unary-operation NaN propagation agrees with the shared helper. -/
def spec_unopNanPl64_def (impl : RepoImpl) : Prop :=
  ∀ (x : Binary64),
    impl.flocq.unopNanPl64 x = BinaryFloat.nan false 1

/-- Binary32 ternary-operation NaN propagation agrees with the shared helper. -/
def spec_ternopNanPl32_def (impl : RepoImpl) : Prop :=
  ∀ (x y z : Binary32),
    impl.flocq.ternopNanPl32 x y z = BinaryFloat.nan false 1

/-- Binary64 ternary-operation NaN propagation agrees with the shared helper. -/
def spec_ternopNanPl64_def (impl : RepoImpl) : Prop :=
  ∀ (x y z : Binary64),
    impl.flocq.ternopNanPl64 x y z = BinaryFloat.nan false 1

/-- `splitBits` exposes the fixed sign/exponent/mantissa field split helper. -/
def spec_splitBits_fields (impl : RepoImpl) : Prop :=
  ∀ (mw ew : Nat) (n : Int),
    let body := n % (2 : Int) ^ (mw + ew + 1)
    impl.flocq.splitBits mw ew n =
      (decide (n < 0), body / (2 : Int) ^ mw, body % (2 : Int) ^ mw)

/-- Splitting an encoded float agrees with the dedicated float splitter. -/
def spec_split_bits_of_binary_float_correct (impl : RepoImpl) : Prop :=
  ∀ (mw ew : Int) (x : BinaryFloat (mw + 1) ((2 : Int) ^ (ew - 1).toNat)),
    impl.flocq.splitBits mw.toNat ew.toNat (impl.flocq.bitsOfBinaryFloat mw ew x) =
      impl.flocq.splitBitsOfBinaryFloat mw ew x

/-- The public raw decoder auxiliary agrees with `binaryFloatOfBits`. -/
def spec_binaryFloatOfBitsAux_agrees (impl : RepoImpl) : Prop :=
  ∀ (mw ew n : Int),
    impl.flocq.binaryFloatOfBitsAux mw ew n = impl.flocq.binaryFloatOfBits mw ew n

/-- `binaryFloatOfBits` is a left inverse of `bitsOfBinaryFloat`:
    decoding the encoding of any `BinaryFloat` recovers the original float. -/
def spec_binary_float_of_bits_of_binary_float (impl : RepoImpl) : Prop :=
  ∀ (mw ew : Int) (x : BinaryFloat (mw + 1) ((2 : Int) ^ (ew - 1).toNat)),
  impl.flocq.binaryFloatOfBits mw ew (impl.flocq.bitsOfBinaryFloat mw ew x) = x

/-- `bitsOfBinaryFloat` is a left inverse of `binaryFloatOfBits`:
    encoding the decoding of any integer bit pattern recovers the original bits. -/
def spec_bits_of_binary_float_of_bits (impl : RepoImpl) : Prop :=
  ∀ (mw ew : Int) (n : Int),
  impl.flocq.bitsOfBinaryFloat mw ew (impl.flocq.binaryFloatOfBits mw ew n) = n

/-- `b32OfBits` is the binary32 specialization of `binaryFloatOfBits`. -/
def spec_b32OfBits_def (impl : RepoImpl) : Prop :=
  ∀ (n : Int), impl.flocq.b32OfBits n = impl.flocq.binaryFloatOfBits 23 8 n

/-- `b64OfBits` is the binary64 specialization of `binaryFloatOfBits`. -/
def spec_b64OfBits_def (impl : RepoImpl) : Prop :=
  ∀ (n : Int), impl.flocq.b64OfBits n = impl.flocq.binaryFloatOfBits 52 11 n

/-- `bitsOfB32` is the binary32 specialization of `bitsOfBinaryFloat`. -/
def spec_bitsOfB32_def (impl : RepoImpl) : Prop :=
  ∀ (x : Binary32), impl.flocq.bitsOfB32 x = impl.flocq.bitsOfBinaryFloat 23 8 x

/-- `bitsOfB64` is the binary64 specialization of `bitsOfBinaryFloat`. -/
def spec_bitsOfB64_def (impl : RepoImpl) : Prop :=
  ∀ (x : Binary64), impl.flocq.bitsOfB64 x = impl.flocq.bitsOfBinaryFloat 52 11 x

/-- `b32Plus` is binary32 addition with the binary32 NaN propagation helper. -/
def spec_b32Plus_def (impl : RepoImpl) : Prop :=
  ∀ (mode : RoundingMode) (x y : Binary32),
    impl.flocq.b32Plus mode x y =
      impl.flocq.bplus 24 128 mode impl.flocq.binopNanPl32 x y

/-- `b32Minus` is binary32 subtraction with the binary32 NaN propagation helper. -/
def spec_b32Minus_def (impl : RepoImpl) : Prop :=
  ∀ (mode : RoundingMode) (x y : Binary32),
    impl.flocq.b32Minus mode x y =
      impl.flocq.bminus 24 128 mode impl.flocq.binopNanPl32 x y

/-- `b32Mult` is binary32 multiplication with the binary32 NaN propagation helper. -/
def spec_b32Mult_def (impl : RepoImpl) : Prop :=
  ∀ (mode : RoundingMode) (x y : Binary32),
    impl.flocq.b32Mult mode x y =
      impl.flocq.bmult 24 128 mode impl.flocq.binopNanPl32 x y

/-- `b32Div` is binary32 division with the binary32 NaN propagation helper. -/
def spec_b32Div_def (impl : RepoImpl) : Prop :=
  ∀ (mode : RoundingMode) (x y : Binary32),
    impl.flocq.b32Div mode x y =
      impl.flocq.bdiv 24 128 mode impl.flocq.binopNanPl32 x y

/-- `b32Sqrt` is binary32 square root with the binary32 NaN propagation helper. -/
def spec_b32Sqrt_def (impl : RepoImpl) : Prop :=
  ∀ (mode : RoundingMode) (x : Binary32),
    impl.flocq.b32Sqrt mode x =
      impl.flocq.bsqrt 24 128 mode impl.flocq.unopNanPl32 x

/-- `b32Fma` is binary32 fused multiply-add with the binary32 NaN propagation helper. -/
def spec_b32Fma_def (impl : RepoImpl) : Prop :=
  ∀ (mode : RoundingMode) (x y z : Binary32),
    impl.flocq.b32Fma mode x y z =
      impl.flocq.bfma 24 128 mode impl.flocq.ternopNanPl32 x y z

/-- `b64Plus` is binary64 addition with the binary64 NaN propagation helper. -/
def spec_b64Plus_def (impl : RepoImpl) : Prop :=
  ∀ (mode : RoundingMode) (x y : Binary64),
    impl.flocq.b64Plus mode x y =
      impl.flocq.bplus 53 1024 mode impl.flocq.binopNanPl64 x y

/-- `b64Minus` is binary64 subtraction with the binary64 NaN propagation helper. -/
def spec_b64Minus_def (impl : RepoImpl) : Prop :=
  ∀ (mode : RoundingMode) (x y : Binary64),
    impl.flocq.b64Minus mode x y =
      impl.flocq.bminus 53 1024 mode impl.flocq.binopNanPl64 x y

/-- `b64Mult` is binary64 multiplication with the binary64 NaN propagation helper. -/
def spec_b64Mult_def (impl : RepoImpl) : Prop :=
  ∀ (mode : RoundingMode) (x y : Binary64),
    impl.flocq.b64Mult mode x y =
      impl.flocq.bmult 53 1024 mode impl.flocq.binopNanPl64 x y

/-- `b64Div` is binary64 division with the binary64 NaN propagation helper. -/
def spec_b64Div_def (impl : RepoImpl) : Prop :=
  ∀ (mode : RoundingMode) (x y : Binary64),
    impl.flocq.b64Div mode x y =
      impl.flocq.bdiv 53 1024 mode impl.flocq.binopNanPl64 x y

/-- `b64Sqrt` is binary64 square root with the binary64 NaN propagation helper. -/
def spec_b64Sqrt_def (impl : RepoImpl) : Prop :=
  ∀ (mode : RoundingMode) (x : Binary64),
    impl.flocq.b64Sqrt mode x =
      impl.flocq.bsqrt 53 1024 mode impl.flocq.unopNanPl64 x

/-- `b64Fma` is binary64 fused multiply-add with the binary64 NaN propagation helper. -/
def spec_b64Fma_def (impl : RepoImpl) : Prop :=
  ∀ (mode : RoundingMode) (x y z : Binary64),
    impl.flocq.b64Fma mode x y z =
      impl.flocq.bfma 53 1024 mode impl.flocq.ternopNanPl64 x y z
