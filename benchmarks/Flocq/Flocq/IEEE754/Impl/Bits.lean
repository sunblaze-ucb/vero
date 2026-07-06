import Flocq.Core.Impl.Defs
import Flocq.IEEE754.Impl.BinaryDefs

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Flocq.IEEE754.Impl.Bits

IEEE 754 bit-pattern encoding/decoding and single/double-precision arithmetic
for the Flocq floating-point formalization, translated from `src/IEEE754/Bits.v`.

`bitsOfBinaryFloat` and `binaryFloatOfBits` form a bijection between binary
floats and their IEEE 754 integer bit patterns. The `b32*` / `b64*` families
specialise these and the standard arithmetic operations to 32-bit and 64-bit
precision respectively.

Types and signatures are fixed vocabulary (DO NOT MODIFY). Implement only the
function bodies inside the `!benchmark code` markers.
-/

-- ── BinaryFloat type: shared with IEEE754.Binary (DO NOT MODIFY) ──────────────
-- `BinaryFloat` is defined in `Impl/IEEE754.BinaryDefs.lean` (imported above).
-- It is separated to avoid a Lean 4 parser conflict between
-- `notation:max "|" a "|"` (from Core.FLT) and inductive constructor `|`.

-- ── Type aliases (DO NOT MODIFY) ─────────────────────────────────────────────

/-- IEEE 754 single-precision floating-point (binary32): prec = 24, emax = 128. -/
abbrev Binary32 := BinaryFloat 24 128

/-- IEEE 754 double-precision floating-point (binary64): prec = 53, emax = 1024. -/
abbrev Binary64 := BinaryFloat 53 1024

-- ── Spec helpers (no markers — fixed vocabulary) ─────────────────────────────

/-- Combine (sign, exponent, mantissa) fields into a signed integer bit pattern.
    The sign bit occupies position `mw + ew`; exponent occupies bits `mw..mw+ew-1`;
    mantissa occupies bits `0..mw-1`. -/
def joinBits (mw ew : Nat) (sign : Bool) (e m : Int) : Int :=
  (if sign then -((2 : Int) ^ (mw + ew)) else 0) + e * (2 : Int) ^ mw + m

/-- Split an integer bit pattern into `(sign, exponent, mantissa)` fields.
    The sign is `x < 0`; exponent and mantissa are extracted from
    `x mod 2^(mw+ew+1)`. -/
def splitBits (mw ew : Nat) (x : Int) : Bool × Int × Int :=
  let body := x % (2 : Int) ^ (mw + ew + 1)
  (x < 0, body / (2 : Int) ^ mw, body % (2 : Int) ^ mw)

/-- Default NaN for binary32 binary operations. -/
def binopNanPl32 (_ _ : Binary32) : Binary32 := BinaryFloat.nan false 1

/-- Default NaN for binary64 binary operations. -/
def binopNanPl64 (_ _ : Binary64) : Binary64 := BinaryFloat.nan false 1

/-- Default NaN for binary32 unary operations. -/
def unopNanPl32 (_ : Binary32) : Binary32 := BinaryFloat.nan false 1

/-- Default NaN for binary64 unary operations. -/
def unopNanPl64 (_ : Binary64) : Binary64 := BinaryFloat.nan false 1

/-- Default NaN for binary32 ternary (fma) operations. -/
def ternopNanPl32 (_ _ _ : Binary32) : Binary32 := BinaryFloat.nan false 1

/-- Default NaN for binary64 ternary (fma) operations. -/
def ternopNanPl64 (_ _ _ : Binary64) : Binary64 := BinaryFloat.nan false 1

/-- Default NaN constant for binary32. -/
def defaultNanPl32 : Binary32 := BinaryFloat.nan false 1

/-- Default NaN constant for binary64. -/
def defaultNanPl64 : Binary64 := BinaryFloat.nan false 1

/-- Validity predicate for a BinaryFloat (axiomatized from Flocq's `valid_binary`). -/
axiom validBinary : ∀ (prec emax : Int), BinaryFloat prec emax → Bool

/-- Internal helper that converts a raw integer bit pattern to a BinaryFloat.
    The result is always valid (see `binaryFloatOfBitsAuxCorrect`). -/
axiom binaryFloatOfBitsAux : ∀ (mw ew : Int), Int → BinaryFloat (mw + 1) ((2 : Int) ^ (ew - 1).toNat)

/-- `binaryFloatOfBitsAux` always produces a valid BinaryFloat. -/
axiom binaryFloatOfBitsAuxCorrect : ∀ (mw ew : Int) (x : Int),
  validBinary (mw + 1) ((2 : Int) ^ (ew - 1).toNat) (binaryFloatOfBitsAux mw ew x) = true

-- ── Axiomatized IEEE 754 binary arithmetic (from IEEE754.Binary) ──────────────
-- These operations are defined in the Binary module; axiomatized here so that
-- this module compiles independently.

/-- IEEE 754 floating-point addition with NaN propagation. -/
axiom bplus : ∀ (prec emax : Int),
  (BinaryFloat prec emax → BinaryFloat prec emax → BinaryFloat prec emax) →
  RoundingMode → BinaryFloat prec emax → BinaryFloat prec emax → BinaryFloat prec emax

/-- IEEE 754 floating-point subtraction with NaN propagation. -/
axiom bminus : ∀ (prec emax : Int),
  (BinaryFloat prec emax → BinaryFloat prec emax → BinaryFloat prec emax) →
  RoundingMode → BinaryFloat prec emax → BinaryFloat prec emax → BinaryFloat prec emax

/-- IEEE 754 floating-point multiplication with NaN propagation. -/
axiom bmult : ∀ (prec emax : Int),
  (BinaryFloat prec emax → BinaryFloat prec emax → BinaryFloat prec emax) →
  RoundingMode → BinaryFloat prec emax → BinaryFloat prec emax → BinaryFloat prec emax

/-- IEEE 754 floating-point division with NaN propagation. -/
axiom bdiv : ∀ (prec emax : Int),
  (BinaryFloat prec emax → BinaryFloat prec emax → BinaryFloat prec emax) →
  RoundingMode → BinaryFloat prec emax → BinaryFloat prec emax → BinaryFloat prec emax

/-- IEEE 754 floating-point square root with NaN propagation. -/
axiom bsqrt : ∀ (prec emax : Int),
  (BinaryFloat prec emax → BinaryFloat prec emax) →
  RoundingMode → BinaryFloat prec emax → BinaryFloat prec emax

/-- IEEE 754 floating-point fused multiply-add with NaN propagation. -/
axiom bfma : ∀ (prec emax : Int),
  (BinaryFloat prec emax → BinaryFloat prec emax → BinaryFloat prec emax → BinaryFloat prec emax) →
  RoundingMode → BinaryFloat prec emax → BinaryFloat prec emax → BinaryFloat prec emax → BinaryFloat prec emax

namespace Flocq

-- ── API signatures (DO NOT MODIFY) ───────────────────────────────────────────

/-- Signature for `splitBits`: split a raw bit pattern into sign, exponent,
    and mantissa fields. -/
abbrev SplitBitsSig := Nat → Nat → Int → Bool × Int × Int

/-- Signature for `splitBitsOfBinaryFloat`: split the encoded bit pattern of
    a BinaryFloat. -/
abbrev SplitBitsOfBinaryFloatSig :=
  (mw : Int) → (ew : Int) → BinaryFloat (mw + 1) ((2 : Int) ^ (ew - 1).toNat) → Bool × Int × Int

/-- Signature for `binaryFloatOfBitsAux`: raw auxiliary bit decoder. -/
abbrev BinaryFloatOfBitsAuxSig :=
  (mw : Int) → (ew : Int) → Int → BinaryFloat (mw + 1) ((2 : Int) ^ (ew - 1).toNat)

/-- Signature for `validBinary`: validity check for a binary float. -/
abbrev ValidBinarySig := ∀ (prec emax : Int), BinaryFloat prec emax → Bool

/-- Signature for default binary32 NaN propagation in binary operations. -/
abbrev BinopNanPl32Sig := Binary32 → Binary32 → Binary32

/-- Signature for default binary64 NaN propagation in binary operations. -/
abbrev BinopNanPl64Sig := Binary64 → Binary64 → Binary64

/-- Signature for default binary32 NaN propagation in unary operations. -/
abbrev UnopNanPl32Sig := Binary32 → Binary32

/-- Signature for default binary64 NaN propagation in unary operations. -/
abbrev UnopNanPl64Sig := Binary64 → Binary64

/-- Signature for default binary32 NaN propagation in ternary operations. -/
abbrev TernopNanPl32Sig := Binary32 → Binary32 → Binary32 → Binary32

/-- Signature for default binary64 NaN propagation in ternary operations. -/
abbrev TernopNanPl64Sig := Binary64 → Binary64 → Binary64 → Binary64

/-- Signature for `bitsOfBinaryFloat`: encode any BinaryFloat as an integer
    bit pattern using the IEEE 754 layout for `mw`-bit mantissa and `ew`-bit
    exponent fields. -/
abbrev BitsOfBinaryFloatSig :=
  (mw : Int) → (ew : Int) → BinaryFloat (mw + 1) ((2 : Int) ^ (ew - 1).toNat) → Int

/-- Signature for `binaryFloatOfBits`: decode an integer bit pattern to a
    BinaryFloat with `mw`-bit mantissa and `ew`-bit exponent fields. -/
abbrev BinaryFloatOfBitsSig :=
  (mw : Int) → (ew : Int) → Int → BinaryFloat (mw + 1) ((2 : Int) ^ (ew - 1).toNat)

/-- Signature for `b32OfBits`: decode a 32-bit integer to a binary32 float. -/
abbrev B32OfBitsSig := Int → Binary32

/-- Signature for `b64OfBits`: decode a 64-bit integer to a binary64 float. -/
abbrev B64OfBitsSig := Int → Binary64

/-- Signature for `bitsOfB32`: encode a binary32 float as a 32-bit integer. -/
abbrev BitsOfB32Sig := Binary32 → Int

/-- Signature for `bitsOfB64`: encode a binary64 float as a 64-bit integer. -/
abbrev BitsOfB64Sig := Binary64 → Int

/-- Signature for `b32Plus`: single-precision addition. -/
abbrev B32PlusSig := RoundingMode → Binary32 → Binary32 → Binary32

/-- Signature for `b32Minus`: single-precision subtraction. -/
abbrev B32MinusSig := RoundingMode → Binary32 → Binary32 → Binary32

/-- Signature for `b32Mult`: single-precision multiplication. -/
abbrev B32MultSig := RoundingMode → Binary32 → Binary32 → Binary32

/-- Signature for `b32Div`: single-precision division. -/
abbrev B32DivSig := RoundingMode → Binary32 → Binary32 → Binary32

/-- Signature for `b32Sqrt`: single-precision square root. -/
abbrev B32SqrtSig := RoundingMode → Binary32 → Binary32

/-- Signature for `b32Fma`: single-precision fused multiply-add. -/
abbrev B32FmaSig := RoundingMode → Binary32 → Binary32 → Binary32 → Binary32

/-- Signature for `b64Plus`: double-precision addition. -/
abbrev B64PlusSig := RoundingMode → Binary64 → Binary64 → Binary64

/-- Signature for `b64Minus`: double-precision subtraction. -/
abbrev B64MinusSig := RoundingMode → Binary64 → Binary64 → Binary64

/-- Signature for `b64Mult`: double-precision multiplication. -/
abbrev B64MultSig := RoundingMode → Binary64 → Binary64 → Binary64

/-- Signature for `b64Div`: double-precision division. -/
abbrev B64DivSig := RoundingMode → Binary64 → Binary64 → Binary64

/-- Signature for `b64Sqrt`: double-precision square root. -/
abbrev B64SqrtSig := RoundingMode → Binary64 → Binary64

/-- Signature for `b64Fma`: double-precision fused multiply-add. -/
abbrev B64FmaSig := RoundingMode → Binary64 → Binary64 → Binary64 → Binary64

end Flocq

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- ── splitBits ────────────────────────────────────────────────────────────────

-- !benchmark @start code_aux def=splitBits
-- !benchmark @end code_aux def=splitBits

def Flocq.splitBits : Flocq.SplitBitsSig :=
-- !benchmark @start code def=splitBits
  fun mw ew x => _root_.splitBits mw ew x
-- !benchmark @end code def=splitBits

-- ── validBinary / NaN propagation helpers ────────────────────────────────────

-- !benchmark @start code_aux def=validBinary
-- !benchmark @end code_aux def=validBinary

noncomputable def Flocq.validBinary : Flocq.ValidBinarySig :=
-- !benchmark @start code def=validBinary
  fun prec emax x => _root_.validBinary prec emax x
-- !benchmark @end code def=validBinary

-- !benchmark @start code_aux def=binopNanPl32
-- !benchmark @end code_aux def=binopNanPl32

def Flocq.binopNanPl32 : Flocq.BinopNanPl32Sig :=
-- !benchmark @start code def=binopNanPl32
  fun x y => _root_.binopNanPl32 x y
-- !benchmark @end code def=binopNanPl32

-- !benchmark @start code_aux def=binopNanPl64
-- !benchmark @end code_aux def=binopNanPl64

def Flocq.binopNanPl64 : Flocq.BinopNanPl64Sig :=
-- !benchmark @start code def=binopNanPl64
  fun x y => _root_.binopNanPl64 x y
-- !benchmark @end code def=binopNanPl64

-- !benchmark @start code_aux def=unopNanPl32
-- !benchmark @end code_aux def=unopNanPl32

def Flocq.unopNanPl32 : Flocq.UnopNanPl32Sig :=
-- !benchmark @start code def=unopNanPl32
  fun x => _root_.unopNanPl32 x
-- !benchmark @end code def=unopNanPl32

-- !benchmark @start code_aux def=unopNanPl64
-- !benchmark @end code_aux def=unopNanPl64

def Flocq.unopNanPl64 : Flocq.UnopNanPl64Sig :=
-- !benchmark @start code def=unopNanPl64
  fun x => _root_.unopNanPl64 x
-- !benchmark @end code def=unopNanPl64

-- !benchmark @start code_aux def=ternopNanPl32
-- !benchmark @end code_aux def=ternopNanPl32

def Flocq.ternopNanPl32 : Flocq.TernopNanPl32Sig :=
-- !benchmark @start code def=ternopNanPl32
  fun x y z => _root_.ternopNanPl32 x y z
-- !benchmark @end code def=ternopNanPl32

-- !benchmark @start code_aux def=ternopNanPl64
-- !benchmark @end code_aux def=ternopNanPl64

def Flocq.ternopNanPl64 : Flocq.TernopNanPl64Sig :=
-- !benchmark @start code def=ternopNanPl64
  fun x y z => _root_.ternopNanPl64 x y z
-- !benchmark @end code def=ternopNanPl64

-- ── bitsOfBinaryFloat ─────────────────────────────────────────────────────────

-- !benchmark @start code_aux def=bitsOfBinaryFloat
-- !benchmark @end code_aux def=bitsOfBinaryFloat

def Flocq.bitsOfBinaryFloat : Flocq.BitsOfBinaryFloatSig :=
-- !benchmark @start code def=bitsOfBinaryFloat
  fun mw ew x =>
    let mwn := mw.toNat
    let ewn := ew.toNat
    -- Sign bit contribution: place 1 in sign position (mw+ew) for negative
    let sb (s : Bool) : Int := if s then -((2 : Int) ^ (mwn + ewn)) else 0
    -- All-ones exponent field: 2^ew - 1 (used for inf/nan)
    let expMask : Int := (2 : Int) ^ ewn - 1
    match x with
    | BinaryFloat.zero s =>
      -- Signed zero: exponent = 0, mantissa = 0
      sb s
    | BinaryFloat.inf s =>
      -- Infinity: exponent = all-ones, mantissa = 0
      sb s + expMask * (2 : Int) ^ mwn
    | BinaryFloat.nan s pl =>
      -- NaN: exponent = all-ones, mantissa = payload (non-zero)
      sb s + expMask * (2 : Int) ^ mwn + (pl : Int)
    | BinaryFloat.finite s mx ex =>
      -- Normal/subnormal: compute emin = 3 - emax - prec = 2 - 2^(ew-1) - mw
      let mxI : Int := (mx : Int)
      let m := mxI - (2 : Int) ^ mwn
      let eminVal : Int := 2 - (2 : Int) ^ (ewn - 1) - mw
      if 0 ≤ m then
        -- Normal: hidden bit is 1, store mantissa without leading bit,
        -- encode exponent with bias (ex - emin + 1)
        sb s + (ex - eminVal + 1) * (2 : Int) ^ mwn + m
      else
        -- Subnormal: exponent field = 0, mantissa = mx
        sb s + mxI
-- !benchmark @end code def=bitsOfBinaryFloat

-- ── splitBitsOfBinaryFloat ───────────────────────────────────────────────────

-- !benchmark @start code_aux def=splitBitsOfBinaryFloat
-- !benchmark @end code_aux def=splitBitsOfBinaryFloat

def Flocq.splitBitsOfBinaryFloat : Flocq.SplitBitsOfBinaryFloatSig :=
-- !benchmark @start code def=splitBitsOfBinaryFloat
  fun mw ew x => Flocq.splitBits mw.toNat ew.toNat (Flocq.bitsOfBinaryFloat mw ew x)
-- !benchmark @end code def=splitBitsOfBinaryFloat

-- ── binaryFloatOfBitsAux ─────────────────────────────────────────────────────

-- !benchmark @start code_aux def=binaryFloatOfBitsAux
-- !benchmark @end code_aux def=binaryFloatOfBitsAux

noncomputable def Flocq.binaryFloatOfBitsAux : Flocq.BinaryFloatOfBitsAuxSig :=
-- !benchmark @start code def=binaryFloatOfBitsAux
  fun mw ew n => _root_.binaryFloatOfBitsAux mw ew n
-- !benchmark @end code def=binaryFloatOfBitsAux

-- ── binaryFloatOfBits ─────────────────────────────────────────────────────────


noncomputable def Flocq.binaryFloatOfBits : Flocq.BinaryFloatOfBitsSig :=
  fun mw ew n => binaryFloatOfBitsAux mw ew n

-- ── b32OfBits ─────────────────────────────────────────────────────────────────


noncomputable def Flocq.b32OfBits : Flocq.B32OfBitsSig :=
  -- mw = 23, ew = 8 for binary32
  fun n => Flocq.binaryFloatOfBits 23 8 n

-- ── b64OfBits ─────────────────────────────────────────────────────────────────


noncomputable def Flocq.b64OfBits : Flocq.B64OfBitsSig :=
  -- mw = 52, ew = 11 for binary64
  fun n => Flocq.binaryFloatOfBits 52 11 n

-- ── bitsOfB32 ─────────────────────────────────────────────────────────────────

-- !benchmark @start code_aux def=bitsOfB32
-- !benchmark @end code_aux def=bitsOfB32

def Flocq.bitsOfB32 : Flocq.BitsOfB32Sig :=
-- !benchmark @start code def=bitsOfB32
  -- mw = 23, ew = 8 for binary32
  fun x => Flocq.bitsOfBinaryFloat 23 8 x
-- !benchmark @end code def=bitsOfB32

-- ── bitsOfB64 ─────────────────────────────────────────────────────────────────

-- !benchmark @start code_aux def=bitsOfB64
-- !benchmark @end code_aux def=bitsOfB64

def Flocq.bitsOfB64 : Flocq.BitsOfB64Sig :=
-- !benchmark @start code def=bitsOfB64
  -- mw = 52, ew = 11 for binary64
  fun x => Flocq.bitsOfBinaryFloat 52 11 x
-- !benchmark @end code def=bitsOfB64

-- ── b32Plus ───────────────────────────────────────────────────────────────────


noncomputable def Flocq.b32Plus : Flocq.B32PlusSig :=
  fun mode x y => bplus 24 128 binopNanPl32 mode x y

-- ── b32Minus ──────────────────────────────────────────────────────────────────


noncomputable def Flocq.b32Minus : Flocq.B32MinusSig :=
  fun mode x y => bminus 24 128 binopNanPl32 mode x y

-- ── b32Mult ───────────────────────────────────────────────────────────────────


noncomputable def Flocq.b32Mult : Flocq.B32MultSig :=
  fun mode x y => bmult 24 128 binopNanPl32 mode x y

-- ── b32Div ────────────────────────────────────────────────────────────────────


noncomputable def Flocq.b32Div : Flocq.B32DivSig :=
  fun mode x y => bdiv 24 128 binopNanPl32 mode x y

-- ── b32Sqrt ───────────────────────────────────────────────────────────────────


noncomputable def Flocq.b32Sqrt : Flocq.B32SqrtSig :=
  fun mode x => bsqrt 24 128 unopNanPl32 mode x

-- ── b32Fma ────────────────────────────────────────────────────────────────────


noncomputable def Flocq.b32Fma : Flocq.B32FmaSig :=
  fun mode x y z => bfma 24 128 ternopNanPl32 mode x y z

-- ── b64Plus ───────────────────────────────────────────────────────────────────


noncomputable def Flocq.b64Plus : Flocq.B64PlusSig :=
  fun mode x y => bplus 53 1024 binopNanPl64 mode x y

-- ── b64Minus ──────────────────────────────────────────────────────────────────


noncomputable def Flocq.b64Minus : Flocq.B64MinusSig :=
  fun mode x y => bminus 53 1024 binopNanPl64 mode x y

-- ── b64Mult ───────────────────────────────────────────────────────────────────


noncomputable def Flocq.b64Mult : Flocq.B64MultSig :=
  fun mode x y => bmult 53 1024 binopNanPl64 mode x y

-- ── b64Div ────────────────────────────────────────────────────────────────────


noncomputable def Flocq.b64Div : Flocq.B64DivSig :=
  fun mode x y => bdiv 53 1024 binopNanPl64 mode x y

-- ── b64Sqrt ───────────────────────────────────────────────────────────────────


noncomputable def Flocq.b64Sqrt : Flocq.B64SqrtSig :=
  fun mode x => bsqrt 53 1024 unopNanPl64 mode x

-- ── b64Fma ────────────────────────────────────────────────────────────────────


noncomputable def Flocq.b64Fma : Flocq.B64FmaSig :=
  fun mode x y z => bfma 53 1024 ternopNanPl64 mode x y z
