-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Primefac.Impl.Factor

Integer factorization operations over `Nat`. The three APIs are:

* `isprime n` — the primality test, a `Bool`;
* `iterprod xs` — the running product of a list, freezing the product operation
  `iterprod (x :: xs) = x * iterprod xs`;
* `primefac n` — the prime factorization as a `Nat` list in **nondecreasing**
  order, the canonical presentation of the prime multiset.

Types and signatures are fixed vocabulary (DO NOT MODIFY).
-/

namespace Primefac

-- ── API signatures (DO NOT MODIFY) ───────────────────────────

/-- `isprime n`: whether `n` is a prime number — `true` iff `n ≥ 2` and `n`'s
    only divisors are `1` and `n`. -/
abbrev IsprimeSig := Nat → Bool

/-- `iterprod xs`: the product of all elements of `xs` (`1` on the empty list).
    Freezes the running-product operation used by the factorization laws. -/
abbrev IterprodSig := List Nat → Nat

/-- `primefac n`: the prime factorization of `n` as a `Nat` list in
    nondecreasing order (the multiset of prime factors, presented canonically).
    `primefac 1 = []`; `primefac 0 = []`. -/
abbrev PrimefacSig := Nat → List Nat

end Primefac

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- !benchmark @start code_aux def=isprime
-- !benchmark @end code_aux def=isprime

def Primefac.isprime : Primefac.IsprimeSig :=
-- !benchmark @start code def=isprime
  fun n =>
    if n < 2 then false
    else (List.range n).all (fun d => d < 2 || !(n % d == 0))
-- !benchmark @end code def=isprime

-- !benchmark @start code_aux def=iterprod
-- !benchmark @end code_aux def=iterprod

def Primefac.iterprod : Primefac.IterprodSig :=
-- !benchmark @start code def=iterprod
  fun xs => xs.foldr (fun x acc => x * acc) 1
-- !benchmark @end code def=iterprod

-- !benchmark @start code_aux def=primefac
/-- Reference helper carrying a structural `fuel` argument so the recursion is
    total; `primefac` seeds it with enough fuel. -/
def primefacAux : Nat → Nat → Nat → List Nat
  | 0, _, _ => []
  | fuel + 1, n, d =>
    if n < 2 then []
    else if d * d > n then [n]
    else if n % d == 0 then d :: primefacAux fuel (n / d) d
    else primefacAux fuel n (d + 1)
-- !benchmark @end code_aux def=primefac

def Primefac.primefac : Primefac.PrimefacSig :=
-- !benchmark @start code def=primefac
  fun n => primefacAux (2 * n) n 2
-- !benchmark @end code def=primefac
