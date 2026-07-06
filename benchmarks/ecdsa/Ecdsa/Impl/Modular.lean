-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Ecdsa.Impl.Modular

GF(p) modular-arithmetic primitives. API: `inverseMod` (modular multiplicative
inverse of `a` mod `m`), `isOddPrime`, `jacobi` (Legendre symbol for an odd
prime), and `sqrtModPrime` (modular square root). Everything is discrete `Nat`
arithmetic over `%`, `*`, `+`, `-` (Bézout coefficients are `Int`); no `Float`.
All functions are total, terminating `def`s.

Types and signatures are fixed vocabulary (DO NOT MODIFY).
-/

namespace Ecdsa

-- ── API signatures (DO NOT MODIFY) ───────────────────────────

/-- `inverseMod a m`: the modular multiplicative inverse of `a` modulo `m`,
    i.e. the residue `inv ∈ [0, m)` with `(a * inv) % m = 1` when `gcd a m = 1`
    and `m > 1`. -/
abbrev InverseModSig := Nat → Nat → Nat

/-- `isOddPrime n`: whether `n` is an odd prime (`n > 2`, `n` odd, and no proper
    divisor). The curve square-root path's primality guard. -/
abbrev IsOddPrimeSig := Nat → Bool

/-- `jacobi a n`: the Jacobi symbol `(a / n)` for odd `n ≥ 1` (here computed by
    a direct definition for an odd prime `p`, where it is the Legendre symbol).
    Used as the quadratic-residue guard for `sqrtModPrime`. -/
abbrev JacobiSig := Nat → Nat → Int

/-- `sqrtModPrime a p`: a square root of `a` modulo the odd prime `p`, i.e. a
    residue `r ∈ [0, p)` with `(r * r) % p = a % p` when one exists. -/
abbrev SqrtModPrimeSig := Nat → Nat → Nat

end Ecdsa

-- !benchmark @start global_aux
/-- Fuel-bounded extended Euclidean routine on `Int`, returning a `(g, x, y)`
    triple. Curator-provided helper for `inverseMod`. -/
def egcd : Nat → Int → Int → (Int × Int × Int)
  | 0, a, _ => (a, 1, 0)
  | fuel + 1, a, b =>
    if b = 0 then (a, 1, 0)
    else
      let r := egcd fuel b (a % b)
      (r.1, r.2.2, r.2.1 - (a / b) * r.2.2)
-- !benchmark @end global_aux

-- !benchmark @start code_aux def=inverseMod
-- !benchmark @end code_aux def=inverseMod

def Ecdsa.inverseMod : Ecdsa.InverseModSig :=
-- !benchmark @start code def=inverseMod
  fun a m =>
    let r := egcd (a + m + 1) (Int.ofNat (a % m)) (Int.ofNat m)
    (r.2.1 % (Int.ofNat m)).toNat
-- !benchmark @end code def=inverseMod

-- !benchmark @start code_aux def=isOddPrime
/-- `hasDivisorBelow n d`: whether some `k` with `2 ≤ k < d` divides `n`.
    Trial division up to (exclusive) `d`. -/
def hasDivisorBelow (n : Nat) : Nat → Bool
  | 0 => false
  | 1 => false
  | d + 1 => (2 ≤ d && n % d == 0) || hasDivisorBelow n d
-- !benchmark @end code_aux def=isOddPrime

def Ecdsa.isOddPrime : Ecdsa.IsOddPrimeSig :=
-- !benchmark @start code def=isOddPrime
  fun n => 2 < n && n % 2 == 1 && !hasDivisorBelow n n
-- !benchmark @end code def=isOddPrime

-- !benchmark @start code_aux def=jacobi
-- !benchmark @end code_aux def=jacobi

def Ecdsa.jacobi : Ecdsa.JacobiSig :=
-- !benchmark @start code def=jacobi
  fun a p =>
    if p ≤ 1 then 0
    else
      let r := (Nat.pow (a % p) ((p - 1) / 2)) % p
      if r == 0 then 0 else if r == 1 then 1 else -1
-- !benchmark @end code def=jacobi

-- !benchmark @start code_aux def=sqrtModPrime
/-- `findSqrt a p r`: scan residues `r, r-1, …, 0` for one squaring to `a % p`. -/
def findSqrt (a p : Nat) : Nat → Option Nat
  | 0 => if (0 * 0) % p == a % p then some 0 else none
  | r + 1 => if ((r + 1) * (r + 1)) % p == a % p then some (r + 1) else findSqrt a p r
-- !benchmark @end code_aux def=sqrtModPrime

def Ecdsa.sqrtModPrime : Ecdsa.SqrtModPrimeSig :=
-- !benchmark @start code def=sqrtModPrime
  fun a p => (findSqrt a p p).getD 0
-- !benchmark @end code def=sqrtModPrime
