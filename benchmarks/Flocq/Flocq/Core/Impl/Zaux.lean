-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Flocq.Core.Impl.Zaux

Foundation types for the Flocq floating-point formalization, translated from
the Coq source `src/Core/Zaux.v`.

`Radix` is the central type: it packages an integer base value together with
a proof that the value is at least 2. Every floating-point number system in
Flocq is parameterised by a `Radix`.

Types and signatures are fixed vocabulary (DO NOT MODIFY). This module has no
computable API functions — it is a pure type foundation imported by all other
modules.
-/

-- ── Core data types (DO NOT MODIFY) ──────────────────────────────────────────

/-- A radix (base) for a floating-point number system.
    The integer value `val` must be at least 2. -/
structure Radix where
  val : Int
  h   : 2 ≤ val
  deriving Repr

/-- The standard binary radix (base 2). -/
def radix2 : Radix := ⟨2, by omega⟩

namespace Flocq

-- ── API signatures (DO NOT MODIFY) ───────────────────────────────────────────
/-- Signature for `zfastPowPos`: integer exponentiation by a natural exponent. -/
abbrev ZfastPowPosSig := Int → Nat → Int

/-- Signature for `zposDivEuclAux1`: one Euclidean-division helper. -/
abbrev ZposDivEuclAux1Sig := Int → Int → Int × Int

/-- Signature for `zposDivEuclAux`: positive Euclidean-division helper. -/
abbrev ZposDivEuclAuxSig := Int → Int → Int × Int

/-- Signature for `zfastDivEucl`: Euclidean quotient/remainder pair. -/
abbrev ZfastDivEuclSig := Int → Int → Int × Int

/-- Signature for `iterNat`: iterate a function `n` times. -/
abbrev IterNatSig := {α : Type} → (α → α) → Nat → α → α

end Flocq

-- !benchmark @start global_aux
def zpowerPos (v : Int) (e : Nat) : Int :=
  v ^ e

def intDivEucl (a b : Int) : Int × Int :=
  (Int.ediv a b, Int.emod a b)
-- !benchmark @end global_aux

-- !benchmark @start code_aux def=zfastPowPos
-- !benchmark @end code_aux def=zfastPowPos

def Flocq.zfastPowPos : Flocq.ZfastPowPosSig :=
-- !benchmark @start code def=zfastPowPos
  fun v e => zpowerPos v e
-- !benchmark @end code def=zfastPowPos

-- !benchmark @start code_aux def=zposDivEuclAux1
-- !benchmark @end code_aux def=zposDivEuclAux1

def Flocq.zposDivEuclAux1 : Flocq.ZposDivEuclAux1Sig :=
-- !benchmark @start code def=zposDivEuclAux1
  fun a b => intDivEucl a b
-- !benchmark @end code def=zposDivEuclAux1

-- !benchmark @start code_aux def=zposDivEuclAux
-- !benchmark @end code_aux def=zposDivEuclAux

def Flocq.zposDivEuclAux : Flocq.ZposDivEuclAuxSig :=
-- !benchmark @start code def=zposDivEuclAux
  fun a b =>
    if a < b then
      (0, a)
    else if a = b then
      (1, 0)
    else
      intDivEucl a b
-- !benchmark @end code def=zposDivEuclAux

-- !benchmark @start code_aux def=zfastDivEucl
-- !benchmark @end code_aux def=zfastDivEucl

def Flocq.zfastDivEucl : Flocq.ZfastDivEuclSig :=
-- !benchmark @start code def=zfastDivEucl
  fun a b => intDivEucl a b
-- !benchmark @end code def=zfastDivEucl

-- !benchmark @start code_aux def=iterNat
-- !benchmark @end code_aux def=iterNat

def Flocq.iterNat : Flocq.IterNatSig :=
-- !benchmark @start code def=iterNat
  fun {α} f n x =>
    let rec go : Nat → α → α
      | 0, acc => acc
      | k + 1, acc => go k (f acc)
    go n x
-- !benchmark @end code def=iterNat
