import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Flocq.Core.Impl.Zaux

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Flocq.Core.Impl.Raux

Real-number base-power and magnitude vocabulary for the Flocq floating-point
formalization, translated from `src/Core/Raux.v`.

`bpow beta e` computes β^e as a real number: positive powers are iterated
multiplication, negative powers are `1/β^(-e)`. The `MagProp` structure
witnesses the magnitude invariant β^(val-1) ≤ |x| < β^val, and `mag` gives
the unique integer e satisfying that bound for any nonzero x.

Types and signatures are fixed vocabulary (DO NOT MODIFY). Implement only
the `bpow` function body.
-/

-- ── Spec helpers (no bpow dependency; no markers — fixed vocabulary) ──────────

/-- Three-way comparison of two real numbers. -/
noncomputable def Rcompare (x y : ℝ) : Ordering :=
  if x < y then Ordering.lt
  else if x = y then Ordering.eq
  else Ordering.gt

/-- Boolean less-than test for real numbers. -/
noncomputable def RltBool (x y : ℝ) : Bool :=
  if x < y then true else false

/-- Floor function: largest integer ≤ x. -/
noncomputable def Zfloor (x : ℝ) : Int := ⌊x⌋

/-- Ceiling function: smallest integer ≥ x. -/
noncomputable def Zceil (x : ℝ) : Int := ⌈x⌉

/-- Truncation toward zero: floor for non-negative, ceil for negative. -/
noncomputable def Ztrunc (x : ℝ) : Int :=
  if x < 0 then Zceil x else Zfloor x

/-- Magnitude (order of magnitude): the unique integer e such that
    β^(e-1) ≤ |x| < β^e; returns 0 for x = 0. -/
noncomputable def mag (beta : Radix) (x : ℝ) : Int :=
  if x = 0 then 0
  else ⌊Real.log |x| / Real.log (beta.val : ℝ)⌋ + 1

namespace Flocq

-- ── API signatures (DO NOT MODIFY) ───────────────────────────────────────────
abbrev RcompareSig := ℝ → ℝ → Ordering
abbrev RleBoolSig := ℝ → ℝ → Bool
abbrev RltBoolSig := ℝ → ℝ → Bool
abbrev ReqBoolSig := ℝ → ℝ → Bool
abbrev ZtruncSig := ℝ → Int
abbrev ZawaySig := ℝ → Int
abbrev BpowSig := Radix → Int → ℝ
abbrev CondRoppSig := Bool → ℝ → ℝ

noncomputable def mag : Radix → ℝ → Int := _root_.mag

end Flocq

-- !benchmark @start global_aux
noncomputable def RleBool (x y : ℝ) : Bool :=
  if x ≤ y then true else false

noncomputable def ReqBool (x y : ℝ) : Bool :=
  if x = y then true else false

noncomputable def Zaway (x : ℝ) : Int :=
  if x < 0 then Zfloor x else Zceil x
-- !benchmark @end global_aux

-- !benchmark @start code_aux def=rcompare
-- !benchmark @end code_aux def=rcompare

noncomputable def Flocq.rcompare : Flocq.RcompareSig :=
-- !benchmark @start code def=rcompare
  fun x y => Rcompare x y
-- !benchmark @end code def=rcompare

-- !benchmark @start code_aux def=rleBool
-- !benchmark @end code_aux def=rleBool

noncomputable def Flocq.rleBool : Flocq.RleBoolSig :=
-- !benchmark @start code def=rleBool
  fun x y => RleBool x y
-- !benchmark @end code def=rleBool

-- !benchmark @start code_aux def=rltBool
-- !benchmark @end code_aux def=rltBool

noncomputable def Flocq.rltBool : Flocq.RltBoolSig :=
-- !benchmark @start code def=rltBool
  fun x y => RltBool x y
-- !benchmark @end code def=rltBool

-- !benchmark @start code_aux def=reqBool
-- !benchmark @end code_aux def=reqBool

noncomputable def Flocq.reqBool : Flocq.ReqBoolSig :=
-- !benchmark @start code def=reqBool
  fun x y => ReqBool x y
-- !benchmark @end code def=reqBool

-- !benchmark @start code_aux def=ztrunc
-- !benchmark @end code_aux def=ztrunc

noncomputable def Flocq.ztrunc : Flocq.ZtruncSig :=
-- !benchmark @start code def=ztrunc
  fun x => Ztrunc x
-- !benchmark @end code def=ztrunc

-- !benchmark @start code_aux def=zaway
-- !benchmark @end code_aux def=zaway

noncomputable def Flocq.zaway : Flocq.ZawaySig :=
-- !benchmark @start code def=zaway
  fun x => Zaway x
-- !benchmark @end code def=zaway


noncomputable def Flocq.bpow : Flocq.BpowSig :=
  fun beta e => (beta.val : ℝ) ^ e

-- !benchmark @start code_aux def=condRopp
-- !benchmark @end code_aux def=condRopp

noncomputable def Flocq.condRopp : Flocq.CondRoppSig :=
-- !benchmark @start code def=condRopp
  fun b x => if b then -x else x
-- !benchmark @end code def=condRopp

-- ── Type depending on bpow (DO NOT MODIFY) ───────────────────────────────────

/-- Proof witness that `val` is the magnitude of `x` w.r.t. radix `beta`:
    β^(val-1) ≤ |x| < β^val whenever x ≠ 0. -/
structure MagProp (beta : Radix) (x : ℝ) where
  val : Int
  h   : x ≠ 0 → Flocq.bpow beta (val - 1) ≤ |x| ∧ |x| < Flocq.bpow beta val

-- ── Spec helpers depending on bpow (no markers — fixed vocabulary) ─────────────

/-- If β^(e-1) ≤ x < β^e then mag β x = e. -/
axiom magUniquePos : ∀ (beta : Radix) (x : ℝ) (e : Int),
  Flocq.bpow beta (e - 1) ≤ x → x < Flocq.bpow beta e → mag beta x = e
