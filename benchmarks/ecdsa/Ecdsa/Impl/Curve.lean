import Ecdsa.Impl.Modular

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Ecdsa.Impl.Curve

Elliptic-curve group law over GF(p) in affine coordinates. API:
`containsPoint`, `negPoint`, `pointDouble`, `pointAdd`, `scalarMult`.

A curve is the short Weierstrass form `y² = x³ + a·x + b (mod p)`. A `Point` is
either the point at infinity (the group identity) or an affine `(x, y)` with
`Nat` coordinates reduced mod `p`. Everything is discrete `Nat` arithmetic over
`%`, `*`, `+`, `-`; modular division uses `Ecdsa.inverseMod`. No `Float`.
Behaviour is pinned by `Spec/Curve.lean`.

Types and signatures are fixed vocabulary (DO NOT MODIFY).
-/

-- ── Core data types (DO NOT MODIFY) ──────────────────────────

/-- An affine elliptic-curve point over GF(p): the point at infinity (group
    identity) or an affine `(x, y)` with `Nat` coordinates. -/
inductive Point where
  | infinity : Point
  | affine : Nat → Nat → Point
deriving DecidableEq, Repr

/-- A short Weierstrass curve `y² = x³ + a·x + b (mod p)` over GF(p). -/
structure Curve where
  p : Nat
  a : Nat
  b : Nat
deriving Repr

namespace Ecdsa

-- ── API signatures (DO NOT MODIFY) ───────────────────────────

/-- `containsPoint c P`: whether `P` lies on the curve `c` — `true` for
    infinity, and for affine `(x, y)` exactly when `y² ≡ x³ + a·x + b (mod p)`. -/
abbrev ContainsPointSig := Curve → Point → Bool

/-- `negPoint c P`: the group inverse `−P` — infinity for infinity, and
    `(x, −y mod p)` for affine `(x, y)`. -/
abbrev NegPointSig := Curve → Point → Point

/-- `pointDouble c P`: the group doubling `2·P`. -/
abbrev PointDoubleSig := Curve → Point → Point

/-- `pointAdd c P Q`: the group addition `P + Q`. -/
abbrev PointAddSig := Curve → Point → Point → Point

/-- `scalarMult c k P`: scalar multiplication `k·P`, the operation behind ECDSA. -/
abbrev ScalarMultSig := Curve → Nat → Point → Point

end Ecdsa

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- !benchmark @start code_aux def=containsPoint
-- !benchmark @end code_aux def=containsPoint

def Ecdsa.containsPoint : Ecdsa.ContainsPointSig :=
-- !benchmark @start code def=containsPoint
  fun c P =>
    match P with
    | .infinity => true
    | .affine x y =>
      (y * y) % c.p == (((x * x) % c.p * x) % c.p + c.a * x + c.b) % c.p
-- !benchmark @end code def=containsPoint

-- !benchmark @start code_aux def=negPoint
-- !benchmark @end code_aux def=negPoint

def Ecdsa.negPoint : Ecdsa.NegPointSig :=
-- !benchmark @start code def=negPoint
  fun c P =>
    match P with
    | .infinity => .infinity
    | .affine x y => .affine x ((c.p - y % c.p) % c.p)
-- !benchmark @end code def=negPoint

-- !benchmark @start code_aux def=pointDouble
-- !benchmark @end code_aux def=pointDouble

def Ecdsa.pointDouble : Ecdsa.PointDoubleSig :=
-- !benchmark @start code def=pointDouble
  fun c P =>
    match P with
    | .infinity => .infinity
    | .affine x y =>
      if (2 * y) % c.p == 0 then .infinity
      else
        let lam := ((3 * x * x + c.a) * Ecdsa.inverseMod ((2 * y) % c.p) c.p) % c.p
        let x3 := ((lam * lam) % c.p + c.p + c.p - 2 * (x % c.p)) % c.p
        let y3 := ((lam * ((x + c.p - x3 % c.p) % c.p)) % c.p + c.p - y % c.p) % c.p
        .affine x3 y3
-- !benchmark @end code def=pointDouble

-- !benchmark @start code_aux def=pointAdd
-- !benchmark @end code_aux def=pointAdd

def Ecdsa.pointAdd : Ecdsa.PointAddSig :=
-- !benchmark @start code def=pointAdd
  fun c P Q =>
    match P, Q with
    | .infinity, q => q
    | p, .infinity => p
    | .affine x1 y1, .affine x2 y2 =>
      if x1 % c.p == x2 % c.p then
        if (y1 + y2) % c.p == 0 then .infinity
        else Ecdsa.pointDouble c (.affine x1 y1)
      else
        let lam := (((y2 + c.p - y1 % c.p) % c.p) *
                    Ecdsa.inverseMod ((x2 + c.p - x1 % c.p) % c.p) c.p) % c.p
        let x3 := ((lam * lam) % c.p + c.p + c.p - (x1 % c.p + x2 % c.p) % c.p) % c.p
        let y3 := ((lam * ((x1 + c.p - x3 % c.p) % c.p)) % c.p + c.p - y1 % c.p) % c.p
        .affine x3 y3
-- !benchmark @end code def=pointAdd

-- !benchmark @start code_aux def=scalarMult
-- !benchmark @end code_aux def=scalarMult

def Ecdsa.scalarMult : Ecdsa.ScalarMultSig :=
-- !benchmark @start code def=scalarMult
  fun c k P =>
    let rec go : Nat → Point
      | 0 => .infinity
      | n + 1 => Ecdsa.pointAdd c (go n) P
    go k
-- !benchmark @end code def=scalarMult
