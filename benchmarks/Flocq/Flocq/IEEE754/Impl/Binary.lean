import Mathlib.Data.Real.Sqrt
import Flocq.Core.Impl.Ulp
import Flocq.Core.Impl.Defs
import Flocq.IEEE754.Impl.BinaryDefs

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Flocq.IEEE754.Impl.Binary

IEEE 754 binary floating-point representation, translated from the Coq sources
`src/IEEE754/Binary.v` and `src/IEEE754/BinarySingleNaN.v`.

`BinaryFloat prec emax` is the central type: it represents an IEEE 754
floating-point number with `prec`-bit mantissa and `emax`-bounded exponent.
The four constructors mirror Coq's `binary_float`:
- `zero sign` — positive or negative zero
- `inf sign` — positive or negative infinity
- `nan sign payload` — NaN with a nonzero payload
- `finite sign mantissa exponent` — a finite (normal or subnormal) float

Types and signatures are fixed vocabulary (DO NOT MODIFY). Implement only the
function bodies inside the `!benchmark code` markers.
-/

-- ── Core data types (DO NOT MODIFY) ──────────────────────────────────────────
-- `BinaryFloat` is defined in `Impl/IEEE754.BinaryDefs.lean` (imported above).
-- It is separated to avoid a Lean 4 parser conflict between
-- `notation:max "|" a "|"` (from Core.FLT) and inductive constructor `|`.

-- ── Additional spec helpers (DO NOT MODIFY) ───────────────────────────────────

/-- Test whether a `BinaryFloat` is finite (i.e., not infinity or NaN). -/
def isFinite (prec emax : Int) (x : BinaryFloat prec emax) : Bool :=
  match x with
  | BinaryFloat.inf _ => false
  | BinaryFloat.nan _ _ => false
  | _ => true

/-- Test whether a `BinaryFloat` is NaN. -/
def isNaN (prec emax : Int) (x : BinaryFloat prec emax) : Bool :=
  match x with
  | BinaryFloat.nan _ _ => true
  | _ => false

/-- Convert a `BinaryFloat` to its real value.
    - `finite s m e` → `(-1)^s × m × 2^e`
    - `zero`, `inf`, `nan` → 0 (used only for spec purposes on finite inputs) -/
noncomputable def b2R (prec emax : Int) (x : BinaryFloat prec emax) : ℝ :=
  match x with
  | BinaryFloat.finite s m e =>
    let sign : ℝ := if s then -1 else 1
    sign * (m : ℝ) * Flocq.bpow radix2 e
  | _ => 0

/-- Map a `RoundingMode` to its corresponding integer rounding function on ℝ. -/
noncomputable def roundMode (mode : RoundingMode) : (ℝ → Int) :=
  match mode with
  | RoundingMode.DN => Zfloor
  | RoundingMode.UP => Zceil
  | RoundingMode.ZR => Ztrunc
  | RoundingMode.NE => Znearest (fun _ => false)
  | RoundingMode.NA => Znearest (fun _ => true)

/-- Round a real number to the FLT format with given precision and max exponent. -/
noncomputable def rndFLT (prec emax : Int) (mode : RoundingMode) (x : ℝ) : ℝ :=
  Flocq.round radix2 (FLT_exp (2 - prec - emax) prec) (roundMode mode) x

-- ── Private helpers ───────────────────────────────────────────────────────────

/-- The FLT exponent function for standard IEEE binary with `emin = 2 - prec - emax`. -/
private noncomputable def fltFexp (prec emax : Int) : Int → Int :=
  FLT_exp (2 - prec - emax) prec

/-- Extract the sign from any `BinaryFloat`. -/
private def bSign (prec emax : Int) (x : BinaryFloat prec emax) : Bool :=
  match x with
  | BinaryFloat.zero s => s
  | BinaryFloat.inf s => s
  | BinaryFloat.nan s _ => s
  | BinaryFloat.finite s _ _ => s

/-- Convert a rounded real number back to `BinaryFloat`.
    Uses `szero` as the sign of any zero result.
    Assumes `x` is already in the FLT format range. -/
private noncomputable def realToFloat (prec emax : Int) (szero : Bool) (x : ℝ) :
    BinaryFloat prec emax :=
  if x = 0 then BinaryFloat.zero szero
  else
    let e := fltFexp prec emax (Flocq.mag radix2 x)
    if x < 0 then
      let m := Zfloor ((-x) * Flocq.bpow radix2 (-e))
      if m ≤ 0 then BinaryFloat.zero szero
      else BinaryFloat.finite true m.toNat e
    else
      let m := Zfloor (x * Flocq.bpow radix2 (-e))
      if m ≤ 0 then BinaryFloat.zero szero
      else BinaryFloat.finite false m.toNat e

namespace Flocq

-- ── API signatures (DO NOT MODIFY) ───────────────────────────────────────────

/-- b2R: real-value projection for a binary float. -/
abbrev B2RSig :=
  ∀ (prec emax : Int), BinaryFloat prec emax → ℝ

/-- isFinite: test whether a binary float is finite. -/
abbrev IsFiniteSig :=
  ∀ (prec emax : Int), BinaryFloat prec emax → Bool

/-- isNaN: test whether a binary float is NaN. -/
abbrev IsNaNSig :=
  ∀ (prec emax : Int), BinaryFloat prec emax → Bool

/-- roundMode: map IEEE rounding modes to integer rounding functions. -/
abbrev RoundModeSig := RoundingMode → ℝ → Int

/-- B2FF: type-forget conversion (identity in our representation). -/
abbrev B2FFSig :=
  ∀ (prec emax : Int), BinaryFloat prec emax → BinaryFloat prec emax

/-- FF2B: bounded conversion from full_float (identity in our representation). -/
abbrev FF2BSig :=
  ∀ (prec emax : Int), BinaryFloat prec emax → BinaryFloat prec emax

/-- binary_normalize: round the integer mantissa `m × 2^e` to the FLT format. -/
abbrev BinaryNormalizeSig :=
  ∀ (prec emax : Int), RoundingMode → Int → Int → Bool → BinaryFloat prec emax

/-- babs: absolute value; `nanH` produces the NaN result for a NaN input. -/
abbrev BabsSig :=
  ∀ (prec emax : Int),
  (BinaryFloat prec emax → BinaryFloat prec emax) →
  BinaryFloat prec emax → BinaryFloat prec emax

/-- bcompare: three-way comparison; `none` when either operand is NaN. -/
abbrev BcompareSig :=
  ∀ (prec emax : Int),
  BinaryFloat prec emax → BinaryFloat prec emax → Option Ordering

/-- bdiv: IEEE division; `nanH` handles NaN-producing cases. -/
abbrev BdivSig :=
  ∀ (prec emax : Int), RoundingMode →
  (BinaryFloat prec emax → BinaryFloat prec emax → BinaryFloat prec emax) →
  BinaryFloat prec emax → BinaryFloat prec emax → BinaryFloat prec emax

/-- bfma: fused multiply-add; `nanH` handles NaN-producing cases. -/
abbrev BfmaSig :=
  ∀ (prec emax : Int), RoundingMode →
  (BinaryFloat prec emax → BinaryFloat prec emax → BinaryFloat prec emax →
   BinaryFloat prec emax) →
  BinaryFloat prec emax → BinaryFloat prec emax →
  BinaryFloat prec emax → BinaryFloat prec emax

/-- bfrexp: split a float into `(significand, exponent)`. -/
abbrev BfrexpSig :=
  ∀ (prec emax : Int), BinaryFloat prec emax → BinaryFloat prec emax × Int

/-- bldexp: multiply a float by `2^n`, rounding if needed. -/
abbrev BldexpSig :=
  ∀ (prec emax : Int), RoundingMode →
  BinaryFloat prec emax → Int → BinaryFloat prec emax

/-- bmax_float: the largest finite float (for the given sign). -/
abbrev BmaxFloatSig := ∀ (prec emax : Int), Bool → BinaryFloat prec emax

/-- bminus: IEEE subtraction; `nanH` handles NaN-producing cases. -/
abbrev BminusSig :=
  ∀ (prec emax : Int), RoundingMode →
  (BinaryFloat prec emax → BinaryFloat prec emax → BinaryFloat prec emax) →
  BinaryFloat prec emax → BinaryFloat prec emax → BinaryFloat prec emax

/-- bmult: IEEE multiplication; `nanH` handles NaN-producing cases. -/
abbrev BmultSig :=
  ∀ (prec emax : Int), RoundingMode →
  (BinaryFloat prec emax → BinaryFloat prec emax → BinaryFloat prec emax) →
  BinaryFloat prec emax → BinaryFloat prec emax → BinaryFloat prec emax

/-- bnearbyint: round to integer using the given mode. -/
abbrev BnearbyintSig :=
  ∀ (prec emax : Int), RoundingMode →
  BinaryFloat prec emax → BinaryFloat prec emax

/-- bone: the float 1.0. -/
abbrev BoneSig := ∀ (prec emax : Int), BinaryFloat prec emax

/-- bopp: negation; `nanH` handles NaN input. -/
abbrev BoppSig :=
  ∀ (prec emax : Int),
  (BinaryFloat prec emax → BinaryFloat prec emax) →
  BinaryFloat prec emax → BinaryFloat prec emax

/-- bplus: IEEE addition; `nanH` handles NaN-producing cases. -/
abbrev BplusSig :=
  ∀ (prec emax : Int), RoundingMode →
  (BinaryFloat prec emax → BinaryFloat prec emax → BinaryFloat prec emax) →
  BinaryFloat prec emax → BinaryFloat prec emax → BinaryFloat prec emax

/-- bpred: largest float strictly below x. -/
abbrev BpredSig :=
  ∀ (prec emax : Int), BinaryFloat prec emax → BinaryFloat prec emax

/-- bsqrt: IEEE square root; `nanH` handles NaN-producing cases. -/
abbrev BsqrtSig :=
  ∀ (prec emax : Int), RoundingMode →
  (BinaryFloat prec emax → BinaryFloat prec emax) →
  BinaryFloat prec emax → BinaryFloat prec emax

/-- bsucc: smallest float strictly above x. -/
abbrev BsuccSig :=
  ∀ (prec emax : Int), BinaryFloat prec emax → BinaryFloat prec emax

/-- btrunc: truncate toward zero to an integer-valued float. -/
abbrev BtruncSig :=
  ∀ (prec emax : Int), BinaryFloat prec emax → BinaryFloat prec emax

/-- bulp: unit in the last place. -/
abbrev BulpSig :=
  ∀ (prec emax : Int), BinaryFloat prec emax → BinaryFloat prec emax

end Flocq

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- ── API implementations ───────────────────────────────────────────────────────

-- !benchmark @start code_aux def=b2R
-- !benchmark @end code_aux def=b2R

noncomputable def Flocq.b2R : Flocq.B2RSig :=
-- !benchmark @start code def=b2R
  fun prec emax x => _root_.b2R prec emax x
-- !benchmark @end code def=b2R

-- !benchmark @start code_aux def=isFinite
-- !benchmark @end code_aux def=isFinite

def Flocq.isFinite : Flocq.IsFiniteSig :=
-- !benchmark @start code def=isFinite
  fun prec emax x => _root_.isFinite prec emax x
-- !benchmark @end code def=isFinite

-- !benchmark @start code_aux def=isNaN
-- !benchmark @end code_aux def=isNaN

def Flocq.isNaN : Flocq.IsNaNSig :=
-- !benchmark @start code def=isNaN
  fun prec emax x => _root_.isNaN prec emax x
-- !benchmark @end code def=isNaN

-- !benchmark @start code_aux def=roundMode
-- !benchmark @end code_aux def=roundMode

noncomputable def Flocq.roundMode : Flocq.RoundModeSig :=
-- !benchmark @start code def=roundMode
  fun mode x => _root_.roundMode mode x
-- !benchmark @end code def=roundMode

-- !benchmark @start code_aux def=b2FF
-- !benchmark @end code_aux def=b2FF

def Flocq.b2FF : Flocq.B2FFSig :=
-- !benchmark @start code def=b2FF
  fun _prec _emax x => x
-- !benchmark @end code def=b2FF

-- !benchmark @start code_aux def=ff2B
-- !benchmark @end code_aux def=ff2B

def Flocq.ff2B : Flocq.FF2BSig :=
-- !benchmark @start code def=ff2B
  fun _prec _emax x => x
-- !benchmark @end code def=ff2B


noncomputable def Flocq.binaryNormalize : Flocq.BinaryNormalizeSig :=
  fun prec emax mode m e szero =>
    let x : ℝ := (m : ℝ) * Flocq.bpow radix2 e
    realToFloat prec emax szero (rndFLT prec emax mode x)

-- !benchmark @start code_aux def=babs
-- !benchmark @end code_aux def=babs

def Flocq.babs : Flocq.BabsSig :=
-- !benchmark @start code def=babs
  fun _prec _emax absNanH x =>
    match x with
    | BinaryFloat.nan _ _    => absNanH x
    | BinaryFloat.zero _     => BinaryFloat.zero false
    | BinaryFloat.inf _      => BinaryFloat.inf false
    | BinaryFloat.finite _ m e => BinaryFloat.finite false m e
-- !benchmark @end code def=babs


noncomputable def Flocq.bcompare : Flocq.BcompareSig :=
  fun prec emax x y =>
    if isNaN prec emax x || isNaN prec emax y then none
    else match x, y with
    | BinaryFloat.inf false, BinaryFloat.inf false => some Ordering.eq
    | BinaryFloat.inf true,  BinaryFloat.inf true  => some Ordering.eq
    | BinaryFloat.inf false, _                     => some Ordering.gt
    | BinaryFloat.inf true,  _                     => some Ordering.lt
    | _,                     BinaryFloat.inf false  => some Ordering.lt
    | _,                     BinaryFloat.inf true   => some Ordering.gt
    | BinaryFloat.zero _,    BinaryFloat.zero _     => some Ordering.eq
    | _, _ => some (Rcompare (b2R prec emax x) (b2R prec emax y))


noncomputable def Flocq.bdiv : Flocq.BdivSig :=
  fun prec emax mode nanH x y =>
    if isNaN prec emax x || isNaN prec emax y then nanH x y
    else
      let sx := bSign prec emax x
      let sy := bSign prec emax y
      let sz := sx != sy
      let xInf := !isFinite prec emax x
      let yInf := !isFinite prec emax y
      let xZero := if let BinaryFloat.zero _ := x then true else false
      let yZero := if let BinaryFloat.zero _ := y then true else false
      if xInf && yInf then nanH x y         -- ∞/∞ = NaN
      else if xZero && yZero then nanH x y  -- 0/0 = NaN
      else if xInf then BinaryFloat.inf sz  -- ∞/finite = ±∞
      else if yZero then BinaryFloat.inf sz -- finite/0 = ±∞
      else if yInf then BinaryFloat.zero sz -- finite/∞ = ±0
      else if xZero then BinaryFloat.zero sz -- 0/finite = ±0
      else
        realToFloat prec emax false (rndFLT prec emax mode (b2R prec emax x / b2R prec emax y))


noncomputable def Flocq.bfma : Flocq.BfmaSig :=
  fun prec emax mode nanH x y z =>
    if isNaN prec emax x || isNaN prec emax y || isNaN prec emax z then nanH x y z
    else if isFinite prec emax x && isFinite prec emax y && isFinite prec emax z then
      let fma := b2R prec emax x * b2R prec emax y + b2R prec emax z
      realToFloat prec emax false (rndFLT prec emax mode fma)
    else
      let sx := bSign prec emax x
      let sy := bSign prec emax y
      let sz := bSign prec emax z
      let xInf := !isFinite prec emax x
      let yInf := !isFinite prec emax y
      let zInf := !isFinite prec emax z
      let xZero := if let BinaryFloat.zero _ := x then true else false
      let yZero := if let BinaryFloat.zero _ := y then true else false
      if (xInf && yZero) || (xZero && yInf) then nanH x y z  -- ∞×0 = NaN
      else if xInf || yInf then
        let sp := sx != sy
        if zInf && (sp != sz) then nanH x y z  -- ±∞ + ∓∞ = NaN
        else BinaryFloat.inf sp
      else z  -- finite×finite + ∞ = ∞ (z is ∞ here)


noncomputable def Flocq.bfrexp : Flocq.BfrexpSig :=
  fun prec emax x =>
    match x with
    | BinaryFloat.finite _ _ _ =>
      let e := Flocq.mag radix2 (b2R prec emax x)
      -- Significand: x × 2^(-e) lies in [0.5, 1)
      let sig := realToFloat prec emax false (b2R prec emax x * Flocq.bpow radix2 (-e))
      (sig, e)
    | _ => (x, 0)


noncomputable def Flocq.bldexp : Flocq.BldexpSig :=
  fun prec emax mode x n =>
    match x with
    | BinaryFloat.finite _ _ _ =>
      realToFloat prec emax false
        (rndFLT prec emax mode (b2R prec emax x * Flocq.bpow radix2 n))
    | _ => x

-- !benchmark @start code_aux def=bmaxFloat
-- !benchmark @end code_aux def=bmaxFloat

def Flocq.bmaxFloat : Flocq.BmaxFloatSig :=
-- !benchmark @start code def=bmaxFloat
  fun prec emax s =>
    -- Max float: mantissa = 2^prec - 1, exponent = emax - prec
    let m : Nat := 2 ^ prec.toNat - 1
    let e : Int := emax - prec
    BinaryFloat.finite s m e
-- !benchmark @end code def=bmaxFloat


noncomputable def Flocq.bminus : Flocq.BminusSig :=
  fun prec emax mode nanH x y =>
    if isNaN prec emax x || isNaN prec emax y then nanH x y
    else if !isFinite prec emax x || !isFinite prec emax y then
      let sx := bSign prec emax x
      let sy := bSign prec emax y
      match x, y with
      | BinaryFloat.inf _, BinaryFloat.inf _ =>
        -- +∞ - -∞ = +∞; +∞ - +∞ = NaN; -∞ - +∞ = -∞; -∞ - -∞ = NaN
        if sx != sy then BinaryFloat.inf sx else nanH x y
      | BinaryFloat.inf _, _ => BinaryFloat.inf sx
      | _, BinaryFloat.inf _ => BinaryFloat.inf !sy
      | _, _ => nanH x y
    else
      let diff := b2R prec emax x - b2R prec emax y
      realToFloat prec emax (mode == RoundingMode.DN) (rndFLT prec emax mode diff)


noncomputable def Flocq.bmult : Flocq.BmultSig :=
  fun prec emax mode nanH x y =>
    if isNaN prec emax x || isNaN prec emax y then nanH x y
    else
      let sx := bSign prec emax x
      let sy := bSign prec emax y
      let sz := sx != sy
      let xInf := !isFinite prec emax x
      let yInf := !isFinite prec emax y
      let xZero := if let BinaryFloat.zero _ := x then true else false
      let yZero := if let BinaryFloat.zero _ := y then true else false
      if (xInf && yZero) || (xZero && yInf) then nanH x y  -- ∞×0 = NaN
      else if xInf || yInf then BinaryFloat.inf sz
      else if xZero || yZero then BinaryFloat.zero sz
      else
        realToFloat prec emax sz (rndFLT prec emax mode (b2R prec emax x * b2R prec emax y))


noncomputable def Flocq.bnearbyint : Flocq.BnearbyintSig :=
  fun prec emax mode x =>
    match x with
    | BinaryFloat.finite _ _ _ =>
      let rounded : Int := roundMode mode (b2R prec emax x)
      realToFloat prec emax false (rounded : ℝ)
    | _ => x

-- !benchmark @start code_aux def=bone
-- !benchmark @end code_aux def=bone

def Flocq.bone : Flocq.BoneSig :=
-- !benchmark @start code def=bone
  fun _prec _emax => BinaryFloat.finite false 1 0
-- !benchmark @end code def=bone

-- !benchmark @start code_aux def=bopp
-- !benchmark @end code_aux def=bopp

def Flocq.bopp : Flocq.BoppSig :=
-- !benchmark @start code def=bopp
  fun _prec _emax oppNanH x =>
    match x with
    | BinaryFloat.nan _ _      => oppNanH x
    | BinaryFloat.zero s       => BinaryFloat.zero !s
    | BinaryFloat.inf s        => BinaryFloat.inf !s
    | BinaryFloat.finite s m e => BinaryFloat.finite (!s) m e
-- !benchmark @end code def=bopp


noncomputable def Flocq.bplus : Flocq.BplusSig :=
  fun prec emax mode nanH x y =>
    if isNaN prec emax x || isNaN prec emax y then nanH x y
    else if !isFinite prec emax x || !isFinite prec emax y then
      match x, y with
      | BinaryFloat.inf sx, BinaryFloat.inf sy =>
        if sx == sy then BinaryFloat.inf sx else nanH x y
      | BinaryFloat.inf sx, _ => BinaryFloat.inf sx
      | _, BinaryFloat.inf sy => BinaryFloat.inf sy
      | _, _ => nanH x y
    else
      let sum := b2R prec emax x + b2R prec emax y
      realToFloat prec emax (mode == RoundingMode.DN) (rndFLT prec emax mode sum)


noncomputable def Flocq.bpred : Flocq.BpredSig :=
  fun prec emax x =>
    match x with
    | BinaryFloat.nan _ _  => x
    | BinaryFloat.inf false =>
      -- predecessor of +∞ is the maximum positive finite float
      Flocq.bmaxFloat prec emax false
    | BinaryFloat.inf true => BinaryFloat.inf true
    | BinaryFloat.zero _ =>
      -- predecessor of 0 is the smallest negative float
      realToFloat prec emax true
        (Flocq.pred radix2 (fltFexp prec emax) 0)
    | BinaryFloat.finite _ _ _ =>
      realToFloat prec emax false
        (Flocq.pred radix2 (fltFexp prec emax) (b2R prec emax x))


noncomputable def Flocq.bsqrt : Flocq.BsqrtSig :=
  fun prec emax mode sqrtNanH x =>
    match x with
    | BinaryFloat.nan _ _      => sqrtNanH x
    | BinaryFloat.zero s       => BinaryFloat.zero s   -- √(±0) = ±0
    | BinaryFloat.inf false    => BinaryFloat.inf false -- √(+∞) = +∞
    | BinaryFloat.inf true     => sqrtNanH x            -- √(-∞) = NaN
    | BinaryFloat.finite true _ _ => sqrtNanH x         -- √(negative) = NaN
    | BinaryFloat.finite false _ _ =>
      realToFloat prec emax false
        (rndFLT prec emax mode (Real.sqrt (b2R prec emax x)))


noncomputable def Flocq.bsucc : Flocq.BsuccSig :=
  fun prec emax x =>
    match x with
    | BinaryFloat.nan _ _  => x
    | BinaryFloat.inf false => BinaryFloat.inf false
    | BinaryFloat.inf true =>
      -- successor of -∞ is the most negative finite float
      Flocq.bmaxFloat prec emax true
    | BinaryFloat.zero _ =>
      -- successor of 0 is the smallest positive float
      realToFloat prec emax false
        (Flocq.succ radix2 (fltFexp prec emax) 0)
    | BinaryFloat.finite _ _ _ =>
      realToFloat prec emax false
        (Flocq.succ radix2 (fltFexp prec emax) (b2R prec emax x))


noncomputable def Flocq.btrunc : Flocq.BtruncSig :=
  fun prec emax x =>
    match x with
    | BinaryFloat.finite _ _ _ =>
      realToFloat prec emax false ((Ztrunc (b2R prec emax x) : Int) : ℝ)
    | _ => x


noncomputable def Flocq.bulp : Flocq.BulpSig :=
  fun prec emax x =>
    match x with
    | BinaryFloat.finite _ _ _ =>
      let e := fltFexp prec emax (Flocq.mag radix2 (b2R prec emax x))
      BinaryFloat.finite false 1 e
    | _ => BinaryFloat.zero false
