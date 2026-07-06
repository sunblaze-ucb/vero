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

-- ── IEEE754.Bits: bit-pattern encoding ────────────────────────────────────────

-- signed zero: all bits zero
#guard Flocq.bitsOfB32 (BinaryFloat.zero false) == 0
#guard Flocq.bitsOfB64 (BinaryFloat.zero false) == 0

-- ── IEEE754.PrimFloat: native Float round-trip ────────────────────────────────

-- 1.0 in binary64: sign=0, biased_exp=1023, frac=0
-- → mantissa = 2^52 = 4503599627370496, flocq_exp = 1023 − 1075 = −52
#guard Flocq.prim2B 1.0 == BinaryFloat.finite false 4503599627370496 (-52)
#guard Flocq.b2Prim (BinaryFloat.finite false 4503599627370496 (-52)) == 1.0
