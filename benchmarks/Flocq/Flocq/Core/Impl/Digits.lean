import Flocq.Core.Impl.Zaux

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Flocq.Core.Impl.Digits

Digit-counting utilities for the Flocq floating-point formalization,
translated from the Coq source `src/Core/Digits.v`.

The central API is `zdigits`, which returns the number of digits needed
to represent `|n|` in a given radix β: the smallest `d ≥ 0` such that
`|n| < β^d` (with the special case `zdigits β 0 = 0`).

Types and signatures are fixed vocabulary (DO NOT MODIFY). Implement
only the function bodies inside the `!benchmark code` markers.
-/

namespace Flocq

-- ── API signatures (DO NOT MODIFY) ────────────────────────────────────────────

/-- Signature for `digits2Pnat`: binary digit count on natural numbers. -/
abbrev Digits2PnatSig := Nat → Nat

/-- Signature for `zsumDigit`: finite sum of repeated digit contributions. -/
abbrev ZsumDigitSig := Int → Int → Int

/-- Signature for `zscale`: scale an integer by a radix power. -/
abbrev ZscaleSig := Radix → Int → Int → Int

/-- Signature for `zslice`: extract a radix digit slice. -/
abbrev ZsliceSig := Radix → Int → Int → Int → Int

/-- Signature for `zdigitsAux`: fuelled digit-counting loop. -/
abbrev ZdigitsAuxSig := Int → Int → Int → Int → Nat → Int

/-- Signature for `zdigits`: given a radix and an integer, return the
    number of digits needed to represent |n| in that radix. -/
abbrev ZdigitsSig := Radix → Int → Int

end Flocq

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- !benchmark @start code_aux def=zdigitsAux
-- Helper: iterate at most `fuel` steps, counting the number of base-`beta`
-- digits needed to represent `absN`.  `nb` is the current digit count and
-- `pow` is `beta ^ nb`.  Returns `nb` as soon as `absN < pow`.
def zdigitsAuxCore (absN beta nb pow : Int) : Nat → Int
  | 0 => nb
  | k + 1 =>
    if absN < pow then nb
    else zdigitsAuxCore absN beta (nb + 1) (beta * pow) k
-- !benchmark @end code_aux def=zdigitsAux

-- !benchmark @start code_aux def=digits2Pnat
-- !benchmark @end code_aux def=digits2Pnat

def Flocq.digits2Pnat : Flocq.Digits2PnatSig :=
-- !benchmark @start code def=digits2Pnat
  fun n => if n = 0 then 0 else Nat.log2 n + 1
-- !benchmark @end code def=digits2Pnat

-- !benchmark @start code_aux def=zsumDigit
-- !benchmark @end code_aux def=zsumDigit

def Flocq.zsumDigit : Flocq.ZsumDigitSig :=
-- !benchmark @start code def=zsumDigit
  fun digit k => digit * k
-- !benchmark @end code def=zsumDigit

-- !benchmark @start code_aux def=zscale
-- !benchmark @end code_aux def=zscale

def Flocq.zscale : Flocq.ZscaleSig :=
-- !benchmark @start code def=zscale
  fun r n k =>
    if k < 0 then n / (r.val ^ (-k).toNat)
    else n * (r.val ^ k.toNat)
-- !benchmark @end code def=zscale

-- !benchmark @start code_aux def=zslice
-- !benchmark @end code_aux def=zslice

def Flocq.zslice : Flocq.ZsliceSig :=
-- !benchmark @start code def=zslice
  fun r n k1 k2 =>
    if k2 ≤ k1 then 0
    else (Flocq.zscale r n (-k1)) % (r.val ^ (k2 - k1).toNat)
-- !benchmark @end code def=zslice

def Flocq.zdigitsAux : Flocq.ZdigitsAuxSig :=
-- !benchmark @start code def=zdigitsAux
  fun absN beta nb pow fuel => zdigitsAuxCore absN beta nb pow fuel
-- !benchmark @end code def=zdigitsAux

-- !benchmark @start code_aux def=zdigits
-- !benchmark @end code_aux def=zdigits

def Flocq.zdigits : Flocq.ZdigitsSig :=
-- !benchmark @start code def=zdigits
  fun r n =>
    if n = 0 then 0
    else
      let absN : Int := Int.ofNat n.natAbs
      -- Use |n| + 1 as fuel: for any β ≥ 2 and |n| ≥ 1,
      -- at most log₂(|n|) ≤ |n| iterations are needed.
      Flocq.zdigitsAux absN r.val 1 r.val (n.natAbs + 1)
-- !benchmark @end code def=zdigits
