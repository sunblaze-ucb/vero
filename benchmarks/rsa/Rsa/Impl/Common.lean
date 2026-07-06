-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Rsa.Impl.Common

The number-theoretic primitives underlying RSA key generation:

* `gcd a b` — the greatest common divisor of `a` and `b`.
* `extendedGcd a b` — the Bézout triple `(g, x, y)` with `a*x + b*y = g`
  (over `Int`) and `g = gcd a b`.
* `inverse x n` — the modular multiplicative inverse: the residue
  `inv ∈ [0, n)` with `(x * inv) % n = 1` when `gcd x n = 1`.
* `crt residues moduli` — the Chinese Remainder solution: the value
  `x ∈ [0, ∏ moduli)` congruent to each residue modulo its modulus.

Types and signatures are fixed vocabulary (DO NOT MODIFY). Behaviour is
pinned by `Spec/Common.lean`.
-/

namespace Rsa

-- ── API signatures (DO NOT MODIFY) ───────────────────────────

/-- `gcd a b`: the greatest common divisor of `a` and `b`. -/
abbrev GcdSig := Nat → Nat → Nat

/-- `extendedGcd a b`: the Bézout triple `(g, x, y)` with `a*x + b*y = g`
    over `Int` and `g = gcd a b`. -/
abbrev ExtendedGcdSig := Nat → Nat → (Nat × Int × Int)

/-- `inverse x n`: the modular multiplicative inverse of `x` modulo `n`
    (the unique residue in `[0, n)` with `(x * inverse x n) % n = 1` when
    `gcd x n = 1`). -/
abbrev InverseSig := Nat → Nat → Nat

/-- `crt residues moduli`: the Chinese-Remainder solution congruent to each
    `residues[i]` modulo `moduli[i]`, reduced into `[0, ∏ moduli)`. -/
abbrev CrtSig := List Nat → List Nat → Nat

end Rsa

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- !benchmark @start code_aux def=gcd
-- !benchmark @end code_aux def=gcd

def Rsa.gcd : Rsa.GcdSig :=
-- !benchmark @start code def=gcd
  fun a b => Nat.gcd a b
-- !benchmark @end code def=gcd

-- !benchmark @start code_aux def=extendedGcd
/-- Fuel-driven helper computing the Bézout triple `(g, x, y)` for
    `extendedGcd`; correct once `b < fuel`. -/
def extendedGcdFuel : Nat → Nat → Nat → (Nat × Int × Int)
  | 0, a, _ => (a, 1, 0)
  | fuel + 1, a, b =>
    if b = 0 then (a, 1, 0)
    else
      let r := extendedGcdFuel fuel b (a % b)
      (r.1, r.2.2, r.2.1 - (Int.ofNat (a / b)) * r.2.2)
-- !benchmark @end code_aux def=extendedGcd

def Rsa.extendedGcd : Rsa.ExtendedGcdSig :=
-- !benchmark @start code def=extendedGcd
  fun a b => extendedGcdFuel (a + b + 1) a b
-- !benchmark @end code def=extendedGcd

-- !benchmark @start code_aux def=inverse
-- !benchmark @end code_aux def=inverse

def Rsa.inverse : Rsa.InverseSig :=
-- !benchmark @start code def=inverse
  fun x n => ((Rsa.extendedGcd x n).2.1 % (Int.ofNat n)).toNat
-- !benchmark @end code def=inverse

-- !benchmark @start code_aux def=crt
/-- Product of a list of moduli (the CRT modulus). -/
def listProd (ms : List Nat) : Nat :=
  ms.foldl (· * ·) 1

/-- One CRT accumulation step over the full modulus `N` and a
    `(residue, modulus)` pair. -/
def crtStep (N : Nat) (acc : Nat) (p : Nat × Nat) : Nat :=
  let aᵢ := p.1
  let mᵢ := p.2
  let M := N / mᵢ
  let inv := Rsa.inverse (M % mᵢ) mᵢ
  acc + (aᵢ % mᵢ) * inv * M
-- !benchmark @end code_aux def=crt

def Rsa.crt : Rsa.CrtSig :=
-- !benchmark @start code def=crt
  fun residues moduli =>
    let N := listProd moduli
    let acc := (residues.zip moduli).foldl (crtStep N) 0
    acc % N
-- !benchmark @end code def=crt
