import Flocq.Core.Impl.Zaux
import Flocq.Core.Impl.Defs
import Flocq.Core.Impl.Digits
import Flocq.Calc.Impl.Bracket
import Flocq.Calc.Impl.Operations
import Flocq.Calc.Impl.Round
import Flocq.IEEE754.Impl.BinaryDefs
import Flocq.IEEE754.Impl.Binary
import Flocq.IEEE754.Impl.Bits
import Flocq.IEEE754.Impl.PrimFloat
import Flocq.IEEE754.Spec.Bits

open Flocq

/-!
# Flocq.Test

Executable conformance tests. `#guard` assertions run against the
curator's reference implementations that live INSIDE the `code`
markers in `Impl/*.lean`. Before the LLM sees the benchmark, the
pipeline replaces marker contents with `sorry` — these guards catch
regressions in the reference impls themselves.

DO NOT MODIFY — infrastructure.
-/

-- ── Core.Digits: digit count ──────────────────────────────────────────────────
#guard Flocq.zdigits radix2 0 == 0
#guard Flocq.zdigits radix2 1 == 1
#guard Flocq.zdigits radix2 7 == 3    -- 7 < 2^3 = 8
#guard Flocq.zdigits radix2 8 == 4    -- 8 < 2^4 = 16

-- ── Calc.Operations: exact multiplication ─────────────────────────────────────
#guard Flocq.fmult ⟨3, 2⟩ ⟨5, 1⟩ == ⟨15, 3⟩
#guard Flocq.fmult ⟨0, 5⟩ ⟨7, -2⟩ == ⟨0, 3⟩

-- ── IEEE754.Binary: computable operations ─────────────────────────────────────

-- bone: 1.0 is represented as finite false 1 0 (1 × 2^0 = 1)
#guard Flocq.bone 53 1024 == BinaryFloat.finite false 1 0
#guard Flocq.bone 24 128  == BinaryFloat.finite false 1 0

-- bmaxFloat: largest finite float for double precision
-- mantissa = 2^53 − 1, exponent = 1024 − 53 = 971
#guard Flocq.bmaxFloat 53 1024 false == BinaryFloat.finite false (2 ^ 53 - 1) (1024 - 53)
#guard Flocq.bmaxFloat 53 1024 true  == BinaryFloat.finite true  (2 ^ 53 - 1) (1024 - 53)

-- b2FF and ff2B: identity conversions
#guard Flocq.b2FF 53 1024 (BinaryFloat.zero false) == BinaryFloat.zero false
#guard Flocq.ff2B 53 1024 (BinaryFloat.nan false 1) == BinaryFloat.nan false 1

-- bopp: negation flips sign bit
#guard Flocq.bopp 53 1024 (fun x => x) (BinaryFloat.finite false 5 2) == BinaryFloat.finite true 5 2
#guard Flocq.bopp 53 1024 (fun x => x) (BinaryFloat.zero true) == BinaryFloat.zero false

-- babs: absolute value clears sign bit
#guard Flocq.babs 53 1024 (fun x => x) (BinaryFloat.finite true 5 2) == BinaryFloat.finite false 5 2
#guard Flocq.babs 53 1024 (fun x => x) (BinaryFloat.zero true) == BinaryFloat.zero false

-- Flocq's IEEE convention gives binary32/binary64 their smallest subnormal
-- exponents, and both standard formats satisfy `Prec_lt_emax`.
example : 3 - (128 : Int) - 24 = -149 := by decide
example : 3 - (1024 : Int) - 53 = -1074 := by decide
example : PrecLtEmax 24 128 := ⟨by decide⟩
example : PrecLtEmax 53 1024 := ⟨by decide⟩

-- ── IEEE754.Bits: bit-pattern encoding ────────────────────────────────────────

-- signed zero: all bits zero
#guard Flocq.bitsOfB32 (BinaryFloat.zero false) == 0
#guard Flocq.bitsOfB64 (BinaryFloat.zero false) == 0

-- ── IEEE754.PrimFloat: native Float round-trip ────────────────────────────────

-- 1.0 in binary64: sign=0, biased_exp=1023, frac=0
-- → mantissa = 2^52 = 4503599627370496, flocq_exp = 1023 − 1075 = −52
#guard Flocq.prim2B 1.0 == BinaryFloat.finite false 4503599627370496 (-52)
#guard Flocq.b2Prim (BinaryFloat.finite false 4503599627370496 (-52)) == 1.0

-- Both signs, subnormal/normal boundary, exponent extremes, and NaN payloads.
private def binary64Boundaries : Array UInt64 := #[
  0, 0x8000000000000000, 1, 0x8000000000000001,
  0x000FFFFFFFFFFFFF, 0x0010000000000000, 0x0010000000000001,
  0x8010000000000000, 0x3FF0000000000000, 0x7FEFFFFFFFFFFFFF,
  0xFFEFFFFFFFFFFFFF, 0x7FF0000000000000, 0xFFF0000000000000,
  0x7FF0000000000001, 0x7FF8000000000000, 0xFFFFFFFFFFFFFFFF]

#guard binary64Boundaries.all fun b =>
  Flocq.bitsOfB64 (Flocq.b64OfBits (b.toNat : Int)) == (b.toNat : Int)
#guard binary64Boundaries.all fun b =>
  _root_.validBinary 53 1024 (Flocq.b64OfBits (b.toNat : Int))
#guard binary64Boundaries.all fun b =>
  (Flocq.b2Prim (Flocq.prim2B (Float.ofBits b))).toBits == (Float.ofBits b).toBits
#guard (Float.ofBits 0xFFFFFFFFFFFFFFFF).toBits == 0x7FF8000000000000
#guard Flocq.prim2B (Flocq.b2Prim (.nan true 1)) == BinaryFloat.nan false (2 ^ 51)

-- Exhaust every encoding of a valid small format, including all signed NaNs.
#guard (List.range (2 ^ (1 + 3 + 1))).all fun n =>
  let x := Flocq.binaryFloatOfBits 1 3 n
  Flocq.bitsOfBinaryFloat 1 3 x == (n : Int) && _root_.validBinary 2 4 x

example : _root_.validBinary 53 1024 (.nan false 0) = false := by decide
example : _root_.validBinary 53 1024 (.nan false (2 ^ 52)) = false := by decide
example : _root_.validBinary 53 1024 (.finite false 0 (-1074)) = false := by decide
example : _root_.validBinary 53 1024 (.finite false 1 0) = false := by decide
example : _root_.validBinary 53 1024 (.finite false (2 ^ 52) (-1074)) = true := by decide
example : Flocq.b64OfBits (Flocq.bitsOfB64 (.nan false 0)) ≠ .nan false 0 := by decide

-- Arithmetic wrappers must reduce to the same declarations as the bundle APIs.
example : spec_b32Plus_def canonical := by unfold spec_b32Plus_def; intros; rfl
example : spec_b32Minus_def canonical := by unfold spec_b32Minus_def; intros; rfl
example : spec_b32Mult_def canonical := by unfold spec_b32Mult_def; intros; rfl
example : spec_b32Div_def canonical := by unfold spec_b32Div_def; intros; rfl
example : spec_b32Sqrt_def canonical := by unfold spec_b32Sqrt_def; intros; rfl
example : spec_b32Fma_def canonical := by unfold spec_b32Fma_def; intros; rfl
example : spec_b64Plus_def canonical := by unfold spec_b64Plus_def; intros; rfl
example : spec_b64Minus_def canonical := by unfold spec_b64Minus_def; intros; rfl
example : spec_b64Mult_def canonical := by unfold spec_b64Mult_def; intros; rfl
example : spec_b64Div_def canonical := by unfold spec_b64Div_def; intros; rfl
example : spec_b64Sqrt_def canonical := by unfold spec_b64Sqrt_def; intros; rfl
example : spec_b64Fma_def canonical := by unfold spec_b64Fma_def; intros; rfl
