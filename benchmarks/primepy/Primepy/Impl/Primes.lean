-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Primepy.Impl.Primes

Scaffolded from `benchmark.json` via the python-from-json curation
stage. API signatures are extracted to `abbrev`s; bodies are `sorry`
stubs wrapped in `!benchmark code` markers for the LLM to fill.
-/


namespace Primepy

-- ── API signatures (DO NOT MODIFY) ───────────────────────────
abbrev FactorSig := Int → Int
abbrev CheckSig := Int → Bool
abbrev FactorsSig := Int → List Int
abbrev PhiSig := Int → Int
abbrev FirstSig := Nat → List Nat
abbrev UptoSig := Int → List Int
abbrev BetweenSig := Int → Int → List Int

end Primepy

-- !benchmark @start global_aux
/-- Primality on `Nat`, matching `spec_helper_primeLike`: `2 ≤ n` and no divisor
    in `[2, n)`. Bounded (`List.range n`), so structurally total. -/
def isPrimeNat (n : Nat) : Bool :=
  decide (2 ≤ n) && (List.range n).all (fun d => decide (d < 2 ∨ n % d ≠ 0))
-- !benchmark @end global_aux

-- !benchmark @start code_aux def=factor
/-- Smallest divisor `≥ 2` of `n` (its smallest prime factor), by bounded search
    over `[0, n]`. `factorNat 0 = 0`, `factorNat 1 = 2` (Python `factor 1 = 2`). -/
def factorNat (n : Nat) : Nat :=
  match (List.range (n + 1)).find? (fun d => decide (2 ≤ d ∧ n % d = 0)) with
  | some d => d
  | none => 2
-- !benchmark @end code_aux def=factor

def Primepy.factor : Primepy.FactorSig :=
-- !benchmark @start code def=factor
  fun num =>
    if num < 2 then 2
    else Int.ofNat (factorNat num.toNat)
-- !benchmark @end code def=factor

-- !benchmark @start code_aux def=check
-- !benchmark @end code_aux def=check

def Primepy.check : Primepy.CheckSig :=
-- !benchmark @start code def=check
  fun num => Primepy.factor num = num
-- !benchmark @end code def=check

-- !benchmark @start code_aux def=factors
/-- Prime factorization of `n` on `Nat`, ascending with multiplicity. Fuel = `n`:
    each step divides by `factorNat n ≥ 2`, so the argument strictly shrinks and
    `n` steps always suffice. Structurally total (recursion on the fuel). -/
def factorsNatAux : Nat → Nat → List Nat
  | _, 0 => []
  | n, fuel + 1 =>
      if n < 2 then []
      else
        let f := factorNat n
        f :: factorsNatAux (n / f) fuel

def factorsNat (n : Nat) : List Nat := factorsNatAux n n
-- !benchmark @end code_aux def=factors

def Primepy.factors : Primepy.FactorsSig :=
-- !benchmark @start code def=factors
  fun num =>
    if num < 2 then []
    else (factorsNat num.toNat).map Int.ofNat
-- !benchmark @end code def=factors

-- !benchmark @start code_aux def=phi
-- !benchmark @end code_aux def=phi

def Primepy.phi : Primepy.PhiSig :=
-- !benchmark @start code def=phi
  -- Euler's totient by its counting definition: the number of `k ∈ [1, n]`
  -- coprime to `n`. Bounded (`List.range n.toNat`), structurally total.
  fun num =>
    Int.ofNat
      (((List.range num.toNat).filter
        (fun k => Nat.gcd (k + 1) num.toNat == 1)).length)
-- !benchmark @end code def=phi

-- !benchmark @start code_aux def=first
/-- Factorial, used only as a worst-case search bound for the next prime.
    Euclid guarantees a prime in `(p, p! + 1]`, so `p! + 2` steps always
    suffice; it is a *counter* bound, never materialized as a list. -/
def factNat : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factNat n

/-- Least prime candidate found by scanning upward from `cand`, using `fuel`
    steps. Structurally total (recursion on `fuel`); stops at the first prime,
    so the large `fuel` bound is never actually traversed at runtime. -/
def findPrimeFrom (cand : Nat) : Nat → Nat
  | 0 => cand
  | fuel + 1 => if isPrimeNat cand then cand else findPrimeFrom (cand + 1) fuel

/-- Least prime strictly greater than `p`. Search starts at `p + 1` with a
    provably sufficient bound `p! + 2` (Euclid). -/
def nextPrimeAfter (p : Nat) : Nat := findPrimeFrom (p + 1) (factNat p + 2)

/-- The `k`-th prime, 1-indexed: `nthPrime 1 = 2`, `nthPrime 2 = 3`, … -/
def nthPrime : Nat → Nat
  | 0 => 0
  | k + 1 => nextPrimeAfter (nthPrime k)

/-- The first `n` primes, ascending. -/
def firstPrimes : Nat → List Nat
  | 0 => []
  | k + 1 => firstPrimes k ++ [nthPrime (k + 1)]
-- !benchmark @end code_aux def=first

def Primepy.first : Primepy.FirstSig :=
-- !benchmark @start code def=first
  firstPrimes
-- !benchmark @end code def=first

-- !benchmark @start code_aux def=upto
/-- All primes `≤ n` on `Nat`, ascending. Bounded (`List.range (n+1)`),
    structurally total. -/
def primesUpto (n : Nat) : List Nat := (List.range (n + 1)).filter isPrimeNat
-- !benchmark @end code_aux def=upto

def Primepy.upto : Primepy.UptoSig :=
-- !benchmark @start code def=upto
  fun n =>
    if n < 2 then []
    else (primesUpto n.toNat).map Int.ofNat
-- !benchmark @end code def=upto

-- !benchmark @start code_aux def=between
-- !benchmark @end code_aux def=between

def Primepy.between : Primepy.BetweenSig :=
-- !benchmark @start code def=between
  -- Primes in `(m, n]`: the lower-bound-exclusive view of `upto n`, matching
  -- `spec_between_agrees_with_upto` directly.
  fun m n => (Primepy.upto n).filter (fun p => decide (m < p))
-- !benchmark @end code def=between
