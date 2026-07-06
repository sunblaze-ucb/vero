import Primefac.Impl.Factor

/-!
# Primefac.Test

Executable conformance tests. `#guard` assertions run against the curator's
reference implementations inside the `code` markers in `Impl/Factor.lean`.

DO NOT MODIFY — infrastructure.
-/

open Primefac

-- ── isprime ─────────────────────────────────────────────────────
#guard isprime 0 == false
#guard isprime 1 == false
#guard isprime 2 == true
#guard isprime 3 == true
#guard isprime 4 == false
#guard isprime 17 == true
#guard isprime 18 == false
#guard isprime 97 == true

-- ── iterprod ─────────────────────────────────────────────────────
#guard iterprod [] == 1
#guard iterprod [7] == 7
#guard iterprod [2, 3, 5] == 30
#guard iterprod [2, 2, 2] == 8

-- ── primefac: nondecreasing prime factorization ──────────────────
#guard primefac 1 == ([] : List Nat)
#guard primefac 2 == [2]
#guard primefac 12 == [2, 2, 3]
#guard primefac 17 == [17]                    -- prime → itself
#guard primefac 60 == [2, 2, 3, 5]
#guard primefac 100 == [2, 2, 5, 5]
#guard primefac 97 == [97]
-- product law holds on the reference impl:
#guard iterprod (primefac 360) == 360
#guard primefac 360 == [2, 2, 2, 3, 3, 5]

-- ── deep structural laws on the reference impl ───────────────────
-- primality ⇔ singleton factorization
#guard (isprime 13) == (primefac 13 == [13])
#guard (isprime 14) == (primefac 14 == [14])
-- multiplicativity: Ω-additivity of the total prime-factor count
#guard (primefac (12 * 35)).length == (primefac 12).length + (primefac 35).length
-- per-prime multiplicity additivity (multiplicity of 2 over a product)
#guard ((primefac (24 * 40)).filter (· == 2)).length
        == ((primefac 24).filter (· == 2)).length + ((primefac 40).filter (· == 2)).length
-- exact 2-adic valuation: 2^3 ∣ 24 but ¬ 2^4 ∣ 24, and primefac 24 has three 2s
#guard ((primefac 24).filter (· == 2)).length == 3
#guard decide (2 ^ 3 ∣ 24) && !(decide (2 ^ 4 ∣ 24))
-- squarefree shape: 30 = 2·3·5 has distinct factors; 12 = 2²·3 repeats
#guard primefac 30 == [2, 3, 5]
#guard primefac 12 == [2, 2, 3]
-- prime power: primefac (p^k) is k copies of p
#guard primefac 8 == [2, 2, 2]                 -- 2^3
#guard primefac 81 == [3, 3, 3, 3]             -- 3^4
#guard primefac 8 == List.replicate 3 2
-- exponent-scaled multiplicity: count of 2 in primefac (12^3) == 3 * count in primefac 12
#guard ((primefac (12 ^ 3)).filter (· == 2)).length
        == 3 * ((primefac 12).filter (· == 2)).length
-- exponent-scaled Ω: Ω(12^3) == 3 * Ω(12)
#guard (primefac (12 ^ 3)).length == 3 * (primefac 12).length
-- least prime factor: the head of the sorted factorization is the smallest prime divisor
#guard (primefac 45).head? == some 3           -- 45 = 3·3·5, least prime factor 3
#guard (primefac 91).head? == some 7           -- 91 = 7·13, least prime factor 7
