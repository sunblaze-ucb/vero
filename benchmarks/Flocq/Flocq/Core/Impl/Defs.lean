-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Flocq.Core.Impl.Defs

Foundation types for the Flocq floating-point library. `FloatNum` is the
central floating-point representation (signed mantissa × radix^exponent,
both stored as `Int`), and `RoundingMode` enumerates the five IEEE-style
rounding directions.

Types are fixed vocabulary (DO NOT MODIFY). This module has no computable
API functions — it is a pure type foundation imported by all other modules.
-/

-- ── Core data types (DO NOT MODIFY) ──────────────────────────

/-- A floating-point number with signed integer mantissa `Fnum` and
    signed integer exponent `Fexp`. The represented value is `Fnum × β^Fexp`
    for an implicit radix β. -/
structure FloatNum where
  Fnum : Int
  Fexp : Int
  deriving Repr, DecidableEq, BEq, Inhabited

/-- The five IEEE-style rounding modes:
    - `DN` — round toward negative infinity
    - `UP` — round toward positive infinity
    - `ZR` — round toward zero
    - `NE` — round to nearest, ties to even
    - `NA` — round to nearest, ties away from zero -/
inductive RoundingMode where
  | DN : RoundingMode
  | UP : RoundingMode
  | ZR : RoundingMode
  | NE : RoundingMode
  | NA : RoundingMode
  deriving Repr, DecidableEq, BEq, Inhabited

-- !benchmark @start global_aux
-- !benchmark @end global_aux
