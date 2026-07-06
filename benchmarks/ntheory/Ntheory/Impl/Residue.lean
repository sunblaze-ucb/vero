-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Ntheory.Impl.Residue

Residue-number-theory operations: the quadratic-residue / Legendre / Jacobi
symbols and the modular root / discrete-log / multiplicative-order / totient
functions. Everything is discrete: residues are `Nat`, symbol values are
`Int ∈ {-1, 0, 1}`; there is no `Float`.

* `legendreSymbol` / `isQuadraticResidue` decide quadratic residuosity;
* `jacobiSymbol` extends the Legendre symbol to odd composite denominators;
* `sqrtMod` / `nthrootMod` return the **least** residue root, or `none`;
* `discreteLog` returns the **least** solving exponent, `nOrder` the **least**
  positive period, `totient` the count of units.

Types and signatures are fixed vocabulary (DO NOT MODIFY).
-/

namespace Ntheory

-- ── API signatures (DO NOT MODIFY) ───────────────────────────

/-- `legendreSymbol a p`: the Legendre symbol `(a / p)` as an `Int` in
    `{-1, 0, 1}` — `0` when `p ∣ a`, `1` when `a` is a nonzero quadratic
    residue mod `p`, `-1` otherwise. (Meaningful for odd prime `p`.) -/
abbrev LegendreSymbolSig := Nat → Nat → Int

/-- `isQuadraticResidue a p`: whether `a` is a nonzero quadratic residue
    mod `p` — there is some `x` with `x*x ≡ a (mod p)` and `a ≢ 0`. -/
abbrev IsQuadraticResidueSig := Nat → Nat → Bool

/-- `jacobiSymbol a n`: the Jacobi symbol `(a / n)` as an `Int` in
    `{-1, 0, 1}` for odd `n ≥ 1`, generalising the Legendre symbol by
    multiplicativity in the (odd) denominator. -/
abbrev JacobiSymbolSig := Int → Nat → Int

/-- `sqrtMod a p`: the least residue `r < p` with `r*r ≡ a (mod p)`, or
    `none` if `a` is a non-residue. The least such `r` is canonical. -/
abbrev SqrtModSig := Nat → Nat → Option Nat

/-- `nthrootMod a k p`: the least residue `r < p` with `r^k ≡ a (mod p)`,
    or `none` if no `k`-th root exists. -/
abbrev NthrootModSig := Nat → Nat → Nat → Option Nat

/-- `discreteLog n a b`: the least exponent `x` with `b^x ≡ a (mod n)`, or
    `none` if `a` is not a power of `b` mod `n`. -/
abbrev DiscreteLogSig := Nat → Nat → Nat → Option Nat

/-- `nOrder a n`: the multiplicative order of `a` mod `n` — the least
    positive `k` with `a^k ≡ 1 (mod n)`, or `0` if no such `k ≤ n` exists. -/
abbrev NOrderSig := Nat → Nat → Nat

/-- `totient n`: Euler's totient — the count of integers `1 ≤ i ≤ n` with
    `gcd i n = 1` (so `totient 0 = 0`, `totient 1 = 1`). -/
abbrev TotientSig := Nat → Nat

end Ntheory

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- !benchmark @start code_aux def=isQuadraticResidue
-- !benchmark @end code_aux def=isQuadraticResidue

def Ntheory.isQuadraticResidue : Ntheory.IsQuadraticResidueSig :=
-- !benchmark @start code def=isQuadraticResidue
  fun a p => a % p != 0 && (List.range p).any (fun x => (x * x) % p == a % p)
-- !benchmark @end code def=isQuadraticResidue

-- !benchmark @start code_aux def=legendreSymbol
-- !benchmark @end code_aux def=legendreSymbol

def Ntheory.legendreSymbol : Ntheory.LegendreSymbolSig :=
-- !benchmark @start code def=legendreSymbol
  fun a p =>
    if a % p == 0 then 0
    else if Ntheory.isQuadraticResidue a p then 1 else -1
-- !benchmark @end code def=legendreSymbol

-- !benchmark @start code_aux def=jacobiSymbol
/-- Reduce a possibly-negative `Int` numerator to its residue in `[0, n)`. -/
def jReduce (a : Int) (n : Nat) : Nat :=
  (a % (n : Int)).toNat

/-- Helper for `jacobiAux`: returns the odd part of `m` together with an
    accumulated sign in `{-1, 1}`. `fuel` bounds the descent. -/
def jStrip (n : Nat) : Nat → Nat → Int → (Nat × Int)
  | 0, m, s => (m, s)
  | f + 1, m, s =>
    if m % 2 == 0 then
      let s' := if n % 8 == 3 || n % 8 == 5 then -s else s
      jStrip n f (m / 2) s'
    else (m, s)

/-- Helper computing the Jacobi symbol, with `fuel` bounding the recursion. -/
def jacobiAux : Nat → Nat → Nat → Int
  | 0, _, _ => 1
  | _, 0, _ => 0
  | _, 1, _ => 1
  | fuel + 1, a, n =>
    let a := a % n
    if a == 0 then 0
    else
      let (a', s) := jStrip n (a + 1) a 1
      if a' == 1 then s
      else
        let s' := if a' % 4 == 3 && n % 4 == 3 then -s else s
        s' * jacobiAux fuel n a'
-- !benchmark @end code_aux def=jacobiSymbol

def Ntheory.jacobiSymbol : Ntheory.JacobiSymbolSig :=
-- !benchmark @start code def=jacobiSymbol
  fun a n =>
    if n == 1 then 1
    else if n == 0 then 0
    else
      let a' := jReduce a n
      jacobiAux (a' + n + 2) a' n
-- !benchmark @end code def=jacobiSymbol

-- !benchmark @start code_aux def=sqrtMod
-- !benchmark @end code_aux def=sqrtMod

def Ntheory.sqrtMod : Ntheory.SqrtModSig :=
-- !benchmark @start code def=sqrtMod
  fun a p => (List.range p).find? (fun x => (x * x) % p == a % p)
-- !benchmark @end code def=sqrtMod

-- !benchmark @start code_aux def=nthrootMod
-- !benchmark @end code_aux def=nthrootMod

def Ntheory.nthrootMod : Ntheory.NthrootModSig :=
-- !benchmark @start code def=nthrootMod
  fun a k p => (List.range p).find? (fun x => (x ^ k) % p == a % p)
-- !benchmark @end code def=nthrootMod

-- !benchmark @start code_aux def=discreteLog
-- !benchmark @end code_aux def=discreteLog

def Ntheory.discreteLog : Ntheory.DiscreteLogSig :=
-- !benchmark @start code def=discreteLog
  fun n a b => (List.range n).find? (fun x => (b ^ x) % n == a % n)
-- !benchmark @end code def=discreteLog

-- !benchmark @start code_aux def=nOrder
-- !benchmark @end code_aux def=nOrder

def Ntheory.nOrder : Ntheory.NOrderSig :=
-- !benchmark @start code def=nOrder
  fun a n => ((List.range n).find? (fun k => 0 < k && (a ^ k) % n == 1 % n)).getD 0
-- !benchmark @end code def=nOrder

-- !benchmark @start code_aux def=totient
-- !benchmark @end code_aux def=totient

def Ntheory.totient : Ntheory.TotientSig :=
-- !benchmark @start code def=totient
  fun n => ((List.range n).filter (fun i => Nat.gcd (i + 1) n == 1)).length
-- !benchmark @end code def=totient
