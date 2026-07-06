import Galoistools.Impl.Ring

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Galoistools.Impl.Division

Euclidean division, gcd, extended gcd, and modular exponentiation for
`GF(p)[x]`, ported from SymPy's `sympy/polys/galoistools.py`.

Polynomials are big-endian coeff lists over `GF(p)` (see `Impl/Ring.lean`).

APIs: `gfDiv` (division with remainder, returns `(q, r)` with `f = q·g + r` and
`deg r < deg g`), `gfRem` / `gfQuo` (the remainder / quotient projections),
`gfGcd` (the **monic** gcd), `gfGcdex` (extended Euclid: `(s, t, h)` with
`s·f + t·g = h = gcd`), and `gfPowMod` (`f^n mod g` by repeated squaring).

All are total, terminating `def`s (recursion is fuel-bounded by list length or
the exponent); no `Float`.

Types and signatures are fixed vocabulary (DO NOT MODIFY).
-/

namespace Galoistools

-- ── API signatures (DO NOT MODIFY) ───────────────────────────

/-- `gfDiv f g p`: division with remainder in `GF(p)[x]`. Returns `(q, r)` with
    `f = q·g + r` and `deg r < deg g` (for `g ≠ []`). -/
abbrev GfDivSig := List Nat → List Nat → Nat → (List Nat × List Nat)

/-- `gfRem f g p`: the remainder of dividing `f` by `g` in `GF(p)[x]`. -/
abbrev GfRemSig := List Nat → List Nat → Nat → List Nat

/-- `gfQuo f g p`: the quotient of dividing `f` by `g` in `GF(p)[x]`. -/
abbrev GfQuoSig := List Nat → List Nat → Nat → List Nat

/-- `gfGcd f g p`: the monic greatest common divisor of `f` and `g` in
    `GF(p)[x]` (Euclidean algorithm, result made monic). -/
abbrev GfGcdSig := List Nat → List Nat → Nat → List Nat

/-- `gfGcdex f g p`: extended Euclid — `(s, t, h)` with `h = gcd(f, g)` (monic)
    and `s·f + t·g = h`. -/
abbrev GfGcdexSig := List Nat → List Nat → Nat → (List Nat × List Nat × List Nat)

/-- `gfPowMod f n g p`: `f^n mod g` in `GF(p)[x]`, by repeated squaring. -/
abbrev GfPowModSig := List Nat → Nat → List Nat → Nat → List Nat

end Galoistools

-- !benchmark @start global_aux
namespace Galoistools

/-- `shiftUp k f`: multiply the big-endian polynomial `f` by `x^k`
    (append `k` trailing zeros). Frozen helper. -/
def shiftUp (k : Nat) (f : List Nat) : List Nat :=
  if f = [] then [] else f ++ List.replicate k 0

/-- `scaleP p c f`: scale the big-endian polynomial `f` by the scalar `c` in
    `GF(p)`, reducing modulo `p`. Frozen helper. -/
def scaleP (p c : Nat) (f : List Nat) : List Nat :=
  gfStrip (f.map (fun a => (a * c) % p))

/-- `divCore` performs schoolbook long division, high degree to low. `fuel`
    bounds the recursion by the dividend length. `qacc` is the big-endian
    quotient built so far, and `expDeg` is the degree the NEXT quotient
    coefficient must occupy. At each step: if `deg cur < deg g` stop, appending
    `expDeg + 1` trailing zeros so the quotient reaches degree `0`, with `cur`
    as the remainder; otherwise the leading term cancels at quotient degree
    `s = deg cur − deg g`, so append `expDeg − s` zeros then the coefficient
    `c = leadCoeff cur · invMod (leadCoeff g)`, subtract `c · x^s · g`, and
    recurse with `expDeg = s − 1`. The zero-fill keeps quotient coefficients at
    their true degree slots even when the working degree drops by more than one.
    `expDeg = -1` marks "quotient complete". -/
def divCore (p : Nat) (g : List Nat) : Nat → List Nat → Int → List Nat → (List Nat × List Nat)
  | 0, qacc, _, cur => (gfStrip qacc, gfStrip cur)
  | fuel + 1, qacc, expDeg, cur =>
    let cur := gfStrip cur
    let dg := gfDegree g
    let dc := gfDegree cur
    if dc < dg then
      -- fill remaining low-degree quotient slots (degrees expDeg … 0) with 0
      let fill := List.replicate (expDeg + 1).toNat 0
      (gfStrip (qacc ++ fill), cur)
    else
      let c := (leadCoeff cur * invMod (leadCoeff g) p) % p
      let s := dc - dg
      -- zero-fill the skipped quotient degrees (expDeg down to s+1), then c
      let gap := List.replicate (expDeg - s).toNat 0
      let qacc' := qacc ++ gap ++ [c]
      let sub := shiftUp s.toNat (scaleP p c g)
      let cur' := Galoistools.gfSub cur sub p
      divCore p g fuel qacc' (s - 1) cur'

end Galoistools
-- !benchmark @end global_aux

namespace Galoistools

-- !benchmark @start code_aux def=gfDiv
-- !benchmark @end code_aux def=gfDiv

def gfDiv : GfDivSig :=
-- !benchmark @start code def=gfDiv
  fun f g p =>
    if g = [] then ([], f)
    else if gfDegree f < gfDegree g then ([], gfStrip f)
    else
      -- highest quotient degree = deg f - deg g; need that many + 1 steps
      let (q, r) := divCore p g (f.length + 1) [] (gfDegree f - gfDegree g) f
      (q, r)
-- !benchmark @end code def=gfDiv

-- !benchmark @start code_aux def=gfRem
-- !benchmark @end code_aux def=gfRem

def gfRem : GfRemSig :=
-- !benchmark @start code def=gfRem
  fun f g p => (Galoistools.gfDiv f g p).2
-- !benchmark @end code def=gfRem

-- !benchmark @start code_aux def=gfQuo
-- !benchmark @end code_aux def=gfQuo

def gfQuo : GfQuoSig :=
-- !benchmark @start code def=gfQuo
  fun f g p => (Galoistools.gfDiv f g p).1
-- !benchmark @end code def=gfQuo

-- !benchmark @start code_aux def=gfGcd
/-- `gcdLoop`: fuel-bounded Euclidean loop. Frozen helper for `gfGcd`. -/
def gcdLoop (p : Nat) : Nat → List Nat → List Nat → List Nat
  | 0, f, _ => f
  | fuel + 1, f, g =>
    if g = [] then f
    else gcdLoop p fuel g (Galoistools.gfRem f g p)
-- !benchmark @end code_aux def=gfGcd

def gfGcd : GfGcdSig :=
-- !benchmark @start code def=gfGcd
  fun f g p => (Galoistools.gfMonic (gcdLoop p (f.length + g.length + 1) f g) p).2
-- !benchmark @end code def=gfGcd

-- !benchmark @start code_aux def=gfGcdex
/-- `gcdexLoop`: fuel-bounded extended-Euclid loop tracking Bézout cofactors
    `(r0, r1, s0, s1, t0, t1)`. Frozen helper for `gfGcdex`. -/
def gcdexLoop (p : Nat) :
    Nat → (List Nat × List Nat × List Nat × List Nat × List Nat × List Nat) →
      (List Nat × List Nat × List Nat)
  | 0, (_, r1, _, s1, _, t1) => (s1, t1, r1)
  | fuel + 1, (r0, r1, s0, s1, t0, t1) =>
    let (q, rr) := Galoistools.gfDiv r0 r1 p
    if rr = [] then (s1, t1, r1)
    else
      let (lc, r1') := Galoistools.gfMonic rr p
      let inv := invMod lc p
      let s := Galoistools.gfSub s0 (Galoistools.gfMul q s1 p) p
      let t := Galoistools.gfSub t0 (Galoistools.gfMul q t1 p) p
      let s1' := scaleP p inv s
      let t1' := scaleP p inv t
      gcdexLoop p fuel (r1, r1', s1, s1', t1, t1')
-- !benchmark @end code_aux def=gfGcdex

def gfGcdex : GfGcdexSig :=
-- !benchmark @start code def=gfGcdex
  fun f g p =>
    if f = [] ∧ g = [] then ([1], [], [])
    else
      let (p0, r0) := Galoistools.gfMonic f p
      let (p1, r1) := Galoistools.gfMonic g p
      if f = [] then ([], [invMod p1 p], r1)
      else if g = [] then ([invMod p0 p], [], r0)
      else
        let s0 := [invMod p0 p]
        let t1 := [invMod p1 p]
        gcdexLoop p (f.length + g.length + 2) (r0, r1, s0, [], [], t1)
-- !benchmark @end code def=gfGcdex

-- !benchmark @start code_aux def=gfPowMod
/-- `powModLoop`: fuel-bounded repeated-squaring accumulator. Frozen helper.
    Arguments after the fixed `(p, g)` are `(fuel, n, base, acc)`. -/
def powModLoop (p : Nat) (g : List Nat) : Nat → Nat → List Nat → List Nat → List Nat
  | 0, _, _, acc => acc
  | fuel + 1, n, base, acc =>
    if n = 0 then acc
    else
      let acc' := if n % 2 = 1 then Galoistools.gfRem (Galoistools.gfMul acc base p) g p else acc
      let base' := Galoistools.gfRem (Galoistools.gfMul base base p) g p
      powModLoop p g fuel (n / 2) base' acc'
-- !benchmark @end code_aux def=gfPowMod

def gfPowMod : GfPowModSig :=
-- !benchmark @start code def=gfPowMod
  fun f n g p =>
    if n = 0 then [1]
    else powModLoop p g (n + 1) n (Galoistools.gfRem f g p) [1]
-- !benchmark @end code def=gfPowMod

end Galoistools
