-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Galoistools.Impl.Ring

Ring arithmetic for univariate polynomials over the prime field `GF(p)`,
ported from SymPy's `sympy/polys/galoistools.py`.

A polynomial is a **big-endian** coefficient list of `Nat`: the head `f[0]` is
the leading (highest-degree) coefficient, `f[len-1]` is the constant term, and
the zero polynomial is `[]` (SymPy's convention). Coefficients live in
`GF(p) = {0, …, p-1}`. `gfStrip` removes leading zeros; `gfDegree f = len f - 1`
(so `-1` for the zero polynomial).

APIs in this module: `gfAdd`, `gfSub`, `gfMul`, `gfNeg`, `gfMonic` — the
`GF(p)[x]` ring operations plus the leading-coefficient normalizer. All are
total, terminating `def`s over `Nat`/`Int`; no `Float`.

Types and signatures are fixed vocabulary (DO NOT MODIFY).
-/

namespace Galoistools

-- ── API signatures (DO NOT MODIFY) ───────────────────────────

/-- `gfAdd f g p`: add two `GF(p)[x]` polynomials (big-endian coeff lists). -/
abbrev GfAddSig := List Nat → List Nat → Nat → List Nat

/-- `gfSub f g p`: subtract `g` from `f` in `GF(p)[x]`. -/
abbrev GfSubSig := List Nat → List Nat → Nat → List Nat

/-- `gfMul f g p`: multiply two `GF(p)[x]` polynomials. -/
abbrev GfMulSig := List Nat → List Nat → Nat → List Nat

/-- `gfNeg f p`: negate a `GF(p)[x]` polynomial coefficient-wise. -/
abbrev GfNegSig := List Nat → Nat → List Nat

/-- `gfMonic f p`: return the leading coefficient of `f` together with the monic
    associate `f / lc` (leading coeff scaled to `1`). For `f = []` returns
    `(0, [])`. -/
abbrev GfMonicSig := List Nat → Nat → (Nat × List Nat)

end Galoistools

-- !benchmark @start global_aux
namespace Galoistools

/-- `gfStrip f`: drop leading zeros from a big-endian coeff list.
    Frozen normal-form helper (mirrors SymPy's `gf_strip`). -/
def gfStrip : List Nat → List Nat
  | [] => []
  | a :: as => if a = 0 then gfStrip as else a :: as

/-- `gfDegree f = len f - 1` as an `Int` (so `-1` for the zero polynomial).
    Frozen degree helper (mirrors SymPy's `gf_degree`). -/
def gfDegree (f : List Nat) : Int := (f.length : Int) - 1

/-- `leadCoeff f`: the leading coefficient `f[0]`, or `0` for `f = []`.
    Frozen helper (mirrors SymPy's `gf_LC`). -/
def leadCoeff (f : List Nat) : Nat :=
  match f with
  | [] => 0
  | a :: _ => a

/-- `gfTrunc p f`: reduce every coefficient modulo `p`, then strip leading
    zeros. Frozen normalizer (mirrors SymPy's `gf_trunc`). -/
def gfTrunc (p : Nat) (f : List Nat) : List Nat :=
  gfStrip (f.map (· % p))

/-- `polyEvalRevAux p x l`: little-endian Horner over `l` (`l` head = constant
    term): `[c₀, c₁, c₂]` ↦ `(c₀ + x·(c₁ + x·c₂)) % p`. Frozen helper. -/
def polyEvalRevAux (p x : Nat) : List Nat → Nat
  | [] => 0
  | c :: cs => (c + x * polyEvalRevAux p x cs) % p

/-- `polyEval p f x`: evaluate the big-endian polynomial `f` (head = leading
    coefficient) at the point `x` in `GF(p)`. Equivalently Horner's rule from the
    leading coefficient down: `[a₀, a₁, a₂]` ↦ `((a₀·x + a₁)·x + a₂) % p`. Frozen
    semantic helper — the ring homomorphism `GF(p)[x] → GF(p)` at `x`. -/
def polyEval (p : Nat) (f : List Nat) (x : Nat) : Nat :=
  polyEvalRevAux p x f.reverse

/-- Fuel-bounded extended Euclid on `Int`, returning `(g, x, y)` with
    `a·x + b·y = g`. Curator-provided helper for the modular inverse. -/
def egcdInt : Nat → Int → Int → (Int × Int × Int)
  | 0, a, _ => (a, 1, 0)
  | fuel + 1, a, b =>
    if b = 0 then (a, 1, 0)
    else
      let r := egcdInt fuel b (a % b)
      (r.1, r.2.2, r.2.1 - (a / b) * r.2.2)

/-- `invMod a p`: the multiplicative inverse of `a` in `GF(p)`, i.e. the residue
    `inv ∈ [0, p)` with `(a·inv) % p = 1` when `gcd a p = 1`. Prime-free via
    extended Euclid; mirrors `K.invert` on the field. -/
def invMod (a p : Nat) : Nat :=
  let r := egcdInt (a + p + 1) (Int.ofNat (a % p)) (Int.ofNat p)
  (r.2.1 % (Int.ofNat p)).toNat

/-- `zipAddPad p xs ys`: little-endian pointwise sum modulo `p` of two lists,
    padding the shorter with zeros. Frozen helper. -/
def zipAddPad (p : Nat) : List Nat → List Nat → List Nat
  | [], ys => ys.map (· % p)
  | xs, [] => xs.map (· % p)
  | x :: xs, y :: ys => (x + y) % p :: zipAddPad p xs ys

/-- `zipSubPad p xs ys`: little-endian pointwise difference `(x - y) % p`,
    padding the shorter with zeros. Frozen helper. -/
def zipSubPad (p : Nat) : List Nat → List Nat → List Nat
  | [], ys => ys.map (fun y => (p - y % p) % p)
  | xs, [] => xs.map (· % p)
  | x :: xs, y :: ys => ((x + (p - y % p)) % p) % p :: zipSubPad p xs ys

/-- `convolve p xs ys`: little-endian polynomial product modulo `p`. Frozen
    helper for `gfMul`. Coefficient `k` of the product is
    `∑_{i+j=k} xs[i]·ys[j]`. -/
def convolve (p : Nat) (xs ys : List Nat) : List Nat :=
  match xs with
  | [] => []
  | x :: xs' =>
    -- x·ys ++ (shift-up of convolve xs' ys)
    let head := ys.map (fun y => (x * y) % p)
    let tail := 0 :: convolve p xs' ys
    zipAddPad p head tail

end Galoistools
-- !benchmark @end global_aux

namespace Galoistools

-- !benchmark @start code_aux def=gfAdd
-- !benchmark @end code_aux def=gfAdd

def gfAdd : GfAddSig :=
-- !benchmark @start code def=gfAdd
  fun f g p => gfStrip ((zipAddPad p f.reverse g.reverse).reverse)
-- !benchmark @end code def=gfAdd

-- !benchmark @start code_aux def=gfSub
-- !benchmark @end code_aux def=gfSub

def gfSub : GfSubSig :=
-- !benchmark @start code def=gfSub
  fun f g p => gfStrip ((zipSubPad p f.reverse g.reverse).reverse)
-- !benchmark @end code def=gfSub

-- !benchmark @start code_aux def=gfMul
-- !benchmark @end code_aux def=gfMul

def gfMul : GfMulSig :=
-- !benchmark @start code def=gfMul
  fun f g p =>
    if f = [] ∨ g = [] then []
    else gfStrip ((convolve p f.reverse g.reverse).reverse)
-- !benchmark @end code def=gfMul

-- !benchmark @start code_aux def=gfNeg
-- !benchmark @end code_aux def=gfNeg

def gfNeg : GfNegSig :=
-- !benchmark @start code def=gfNeg
  fun f p => f.map (fun c => (p - c % p) % p)
-- !benchmark @end code def=gfNeg

-- !benchmark @start code_aux def=gfMonic
/-- `gfQuoGround p a f`: divide every coefficient of `f` by the field element
    `a` (multiply by `invMod a p`), reducing modulo `p`. Frozen helper. -/
def gfQuoGround (p a : Nat) (f : List Nat) : List Nat :=
  f.map (fun c => (c * invMod a p) % p)
-- !benchmark @end code_aux def=gfMonic

def gfMonic : GfMonicSig :=
-- !benchmark @start code def=gfMonic
  fun f p =>
    match f with
    | [] => (0, [])
    | a :: _ => if a = 1 then (a, f) else (a, gfQuoGround p a f)
-- !benchmark @end code def=gfMonic

end Galoistools
