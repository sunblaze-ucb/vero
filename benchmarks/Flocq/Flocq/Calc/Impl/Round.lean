import Flocq.Calc.Impl.Bracket
import Flocq.Core.Impl.Digits

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Flocq.Calc.Impl.Round

Rounding utilities for the Flocq floating-point formalization, translated from
the Coq source `src/Calc/Round.v`.

The three API functions implement the core truncation step used when rounding
a real number to a floating-point format:

- `truncateAux` shifts a (mantissa, exponent, location) triple right by `k`
  digits: it divides the mantissa by `β^k`, increments the exponent by `k`,
  and recomputes the location via `newLocation`.
- `truncate` applies this shift when the current exponent is smaller than
  what the precision format `fexp` prescribes; otherwise it is the identity.
- `truncateFIX` performs the same conditional shift for a fixed-exponent
  (FIX / flush-to-zero) format parameterised by a minimum exponent `emin`.

Types and signatures are fixed vocabulary (DO NOT MODIFY). Implement only
the function bodies inside the `!benchmark code` markers.
-/

namespace Flocq

-- ── API signatures (DO NOT MODIFY) ────────────────────────────────────────────

/-- Signature for `condIncr`: conditionally increment an integer. -/
abbrev CondIncrSig := Bool → Int → Int

/-- Signature for `roundSignDN`: directed-down increment choice under a sign. -/
abbrev RoundSignDNSig := Bool → Location → Bool

/-- Signature for `roundUP`: directed-up increment choice. -/
abbrev RoundUPSig := Location → Bool

/-- Signature for `roundSignUP`: directed-up increment choice under a sign. -/
abbrev RoundSignUPSig := Bool → Location → Bool

/-- Signature for `roundZR`: round-toward-zero increment choice under a sign. -/
abbrev RoundZRSig := Bool → Location → Bool

/-- Signature for `roundN`: nearest rounding increment choice. -/
abbrev RoundNSig := Bool → Location → Bool

/-- Signature for `truncateAux`: given a radix `β`, a float triple
    `(m, e, l)` (mantissa, exponent, location), and a non-negative shift
    count `k`, right-shift the triple by `k` digits. The mantissa is
    divided by `β^k`, the exponent is incremented by `k`, and the location
    is updated via `newLocation`. -/
abbrev TruncateAuxSig := Radix → Int × Int × Location → Int → Int × Int × Location

/-- Signature for `truncate`: given a radix `β` and an exponent function
    `fexp : Int → Int`, truncate the float triple so that the exponent meets
    the precision target prescribed by `fexp`. If `k := fexp(zdigits(β,m)+e) - e`
    is positive the triple is shifted right by `k` via `truncateAux`;
    otherwise the triple is returned unchanged. -/
abbrev TruncateSig := Radix → (Int → Int) → Int × Int × Location → Int × Int × Location

/-- Signature for `truncateFIX`: given a radix `β` and a minimum exponent
    `emin`, truncate the float triple so that the exponent is at least
    `emin` (FIX-style flush-to-zero rounding). If `k := emin - e` is
    positive the mantissa is divided by `β^k` and the exponent becomes
    `e + k = emin`; otherwise the triple is returned unchanged. -/
abbrev TruncateFIXSig := Radix → Int → Int × Int × Location → Int × Int × Location

end Flocq

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- ── rounding-choice predicates ───────────────────────────────────────────────

-- !benchmark @start code_aux def=condIncr
-- !benchmark @end code_aux def=condIncr

def Flocq.condIncr : Flocq.CondIncrSig :=
-- !benchmark @start code def=condIncr
  fun b m => if b then m + 1 else m
-- !benchmark @end code def=condIncr

-- !benchmark @start code_aux def=roundSignDN
-- !benchmark @end code_aux def=roundSignDN

def Flocq.roundSignDN : Flocq.RoundSignDNSig :=
-- !benchmark @start code def=roundSignDN
  fun s l =>
    match l with
    | Location.Exact => false
    | Location.Inexact _ => s
-- !benchmark @end code def=roundSignDN

-- !benchmark @start code_aux def=roundUP
-- !benchmark @end code_aux def=roundUP

def Flocq.roundUP : Flocq.RoundUPSig :=
-- !benchmark @start code def=roundUP
  fun l =>
    match l with
    | Location.Exact => false
    | Location.Inexact _ => true
-- !benchmark @end code def=roundUP

-- !benchmark @start code_aux def=roundSignUP
-- !benchmark @end code_aux def=roundSignUP

def Flocq.roundSignUP : Flocq.RoundSignUPSig :=
-- !benchmark @start code def=roundSignUP
  fun s l =>
    match l with
    | Location.Exact => false
    | Location.Inexact _ => !s
-- !benchmark @end code def=roundSignUP

-- !benchmark @start code_aux def=roundZR
-- !benchmark @end code_aux def=roundZR

def Flocq.roundZR : Flocq.RoundZRSig :=
-- !benchmark @start code def=roundZR
  fun s l =>
    match l with
    | Location.Exact => false
    | Location.Inexact _ => s
-- !benchmark @end code def=roundZR

-- !benchmark @start code_aux def=roundN
-- !benchmark @end code_aux def=roundN

def Flocq.roundN : Flocq.RoundNSig :=
-- !benchmark @start code def=roundN
  fun p l =>
    match l with
    | Location.Exact => false
    | Location.Inexact Ordering.lt => false
    | Location.Inexact Ordering.eq => p
    | Location.Inexact Ordering.gt => true
-- !benchmark @end code def=roundN

-- ── truncateAux ───────────────────────────────────────────────────────────────

-- !benchmark @start code_aux def=truncateAux
-- !benchmark @end code_aux def=truncateAux

def Flocq.truncateAux : Flocq.TruncateAuxSig :=
-- !benchmark @start code def=truncateAux
  fun β t k =>
    let m := t.1
    let e := t.2.1
    let l := t.2.2
    let p : Int := β.val ^ k.natAbs
    (m / p, e + k, Flocq.newLocation p (m % p) l)
-- !benchmark @end code def=truncateAux

-- ── truncate ──────────────────────────────────────────────────────────────────

-- !benchmark @start code_aux def=truncate
-- !benchmark @end code_aux def=truncate

def Flocq.truncate : Flocq.TruncateSig :=
-- !benchmark @start code def=truncate
  fun β fexp t =>
    let m := t.1
    let e := t.2.1
    let k : Int := fexp (Flocq.zdigits β m + e) - e
    if 0 < k then Flocq.truncateAux β t k
    else t
-- !benchmark @end code def=truncate

-- ── truncateFIX ───────────────────────────────────────────────────────────────

-- !benchmark @start code_aux def=truncateFIX
-- !benchmark @end code_aux def=truncateFIX

def Flocq.truncateFIX : Flocq.TruncateFIXSig :=
-- !benchmark @start code def=truncateFIX
  fun β emin t =>
    let m := t.1
    let e := t.2.1
    let l := t.2.2
    let k : Int := emin - e
    if 0 < k then
      let p : Int := β.val ^ k.natAbs
      (m / p, e + k, Flocq.newLocation p (m % p) l)
    else t
-- !benchmark @end code def=truncateFIX
