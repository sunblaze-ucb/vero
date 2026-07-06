-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Flocq.IEEE754.Impl.BinaryDefs

Core inductive type for IEEE 754 binary floating-point numbers.

This file is intentionally kept separate from `Impl/IEEE754.Binary.lean` because
`Core.FLT` defines `notation:max "|" a "|"` (absolute value), which conflicts with
the `|` constructor separator in Lean 4 inductive declarations. By placing
`BinaryFloat` here — with no imports from the Core.FLT chain — we avoid the
parsing conflict.

DO NOT MODIFY — this type is fixed vocabulary for the IEEE754.Binary benchmark.
-/

/-- An IEEE 754 binary floating-point number parameterised by precision `prec`
    and maximum exponent `emax`. Corresponds to Coq's `binary_float prec emax`.

    - `zero s`       — ±0 (sign `s = true` for negative zero)
    - `inf s`        — ±∞
    - `nan s pl`     — NaN; `s` is the sign bit, `pl` the mantissa payload (Nat)
    - `finite s m e` — ±m × 2^e where `m : Nat` is the integer mantissa
                       (includes the implicit leading 1 for normals)
                       and `e : Int` is the unbounded exponent -/
inductive BinaryFloat (prec emax : Int) : Type where
  | zero   : Bool → BinaryFloat prec emax
  | inf    : Bool → BinaryFloat prec emax
  | nan    : Bool → Nat → BinaryFloat prec emax
  | finite : Bool → Nat → Int → BinaryFloat prec emax
  deriving Repr, DecidableEq, Inhabited

-- !benchmark @start global_aux
-- !benchmark @end global_aux
