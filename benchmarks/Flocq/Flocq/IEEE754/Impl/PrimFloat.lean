import Flocq.IEEE754.Impl.Bits

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Flocq.IEEE754.Impl.PrimFloat

Interface between Flocq's `BinaryFloat 53 1024` and Lean's native `Float`
(IEEE 754 binary64), translated from the Coq source `src/IEEE754/PrimFloat.v`.

The two API functions form a round-trip isomorphism for well-formed IEEE 754
binary64 values:

- `prim2B (x : Float) : BinaryFloat 53 1024` — decode a native float into
  the Flocq inductive by extracting the IEEE 754 bit fields (sign, biased
  exponent, mantissa) via `Float.toBits`.

- `b2Prim (x : BinaryFloat 53 1024) : Float` — encode a Flocq BinaryFloat
  back to a native float by reconstructing the IEEE 754 bit pattern and
  calling `Float.ofBits`.

Types and signatures are fixed vocabulary (DO NOT MODIFY). Implement only the
function bodies inside the `!benchmark code` markers.
-/

-- !benchmark @start global_aux
-- !benchmark @end global_aux

/-- The native bridge embeds upstream `BinarySingleNaN` using Lean's quiet NaN.
    General bit encoding still preserves every source-valid NaN payload. -/
def primitiveNanCanonical (x : Binary64) : Prop :=
  match x with
  | .nan s pl => s = false ∧ pl = 2 ^ 51
  | _ => True

/-- External bit reinterpretation laws missing from Lean's opaque Float interface.
    Coq's FloatAxioms supplies analogous conversion laws. Keep them explicit
    premises, independent of candidate functions, rather than adding axioms. -/
structure FloatBitsLaws : Prop where
  ofBits_toBits : ∀ x : Float, Float.ofBits x.toBits = x
  toBits_ofBits : ∀ b : UInt64,
    primitiveNanCanonical (_root_.binaryFloatOfBitsAux 52 11 (b.toNat : Int)) →
    (Float.ofBits b).toBits = b

namespace Flocq

-- ── API signatures (DO NOT MODIFY) ───────────────────────────────────────────

/-- Signature for `b2Prim`: convert a Flocq binary64 to Lean's native Float. -/
abbrev B2PrimSig := BinaryFloat 53 1024 → Float

/-- Signature for `prim2B`: convert Lean's native Float to a Flocq binary64. -/
abbrev Prim2BSig := Float → BinaryFloat 53 1024

end Flocq

-- ── Implementation stubs (LLM task) ──────────────────────────────────────────

-- !benchmark @start code_aux def=b2Prim
-- !benchmark @end code_aux def=b2Prim

def Flocq.b2Prim : Flocq.B2PrimSig :=
-- !benchmark @start code def=b2Prim
  fun x => Float.ofBits (Flocq.bitsOfB64 x).toNat.toUInt64
-- !benchmark @end code def=b2Prim

-- !benchmark @start code_aux def=prim2B
-- !benchmark @end code_aux def=prim2B

def Flocq.prim2B : Flocq.Prim2BSig :=
-- !benchmark @start code def=prim2B
  fun x => Flocq.b64OfBits (x.toBits.toNat : Int)
-- !benchmark @end code def=prim2B
