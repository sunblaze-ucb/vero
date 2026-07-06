import Primepy.Impl.Primes
import Primepy.Harness

/-!
# Primepy.Test

Executable conformance tests. `#guard` assertions run against the
`canonical` wiring.

DO NOT MODIFY — infrastructure.
-/

-- Sentinel — proves Test.lean is wired and counts toward the validator's
-- guard tally.
#guard True

-- ── factor (≥3) ─────────────────────────────────────────────
-- factor returns the smallest prime factor; `factor 1 = 2` by Python convention.
#guard canonical.primepy.factor 1 = 2
#guard canonical.primepy.factor 2 = 2
#guard canonical.primepy.factor 9 = 3
#guard canonical.primepy.factor 15 = 3
#guard canonical.primepy.factor 49 = 7

-- ── check (≥3) ──────────────────────────────────────────────
-- check n returns true iff n is prime; defined as factor n = n.
#guard canonical.primepy.check 2 = true
#guard canonical.primepy.check 3 = true
#guard canonical.primepy.check 4 = false
#guard canonical.primepy.check 17 = true
#guard canonical.primepy.check 25 = false

-- ── factors (≥3) ────────────────────────────────────────────
-- factors n returns the prime factorisation of n with multiplicity.
#guard canonical.primepy.factors 12 = [2, 2, 3]
#guard canonical.primepy.factors 60 = [2, 2, 3, 5]
#guard canonical.primepy.factors 7 = [7]
#guard canonical.primepy.factors 100 = [2, 2, 5, 5]

-- ── phi (≥3) ────────────────────────────────────────────────
-- Euler's totient.  phi 9 = 6, phi p = p-1 for prime p.
#guard canonical.primepy.phi 9 = 6
#guard canonical.primepy.phi 7 = 6
#guard canonical.primepy.phi 12 = 4
#guard canonical.primepy.phi 2 = 1

-- ── first (≥3) ──────────────────────────────────────────────
-- first n returns the first n primes as List Nat.
#guard canonical.primepy.first 1 = [2]
#guard canonical.primepy.first 5 = [2, 3, 5, 7, 11]
#guard canonical.primepy.first 10 = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]

-- ── upto (≥3) ───────────────────────────────────────────────
-- upto n returns all primes p ≤ n in ascending order.
#guard canonical.primepy.upto 2 = [2]
#guard canonical.primepy.upto 10 = [2, 3, 5, 7]
#guard canonical.primepy.upto 20 = [2, 3, 5, 7, 11, 13, 17, 19]
#guard canonical.primepy.upto 1 = []

-- ── between (≥3) ────────────────────────────────────────────
-- NOTE (fixed): step-by-1 to match spec.  The upstream Python uses
-- `range(m+d, n+1, 2)` (step 2) which skips even candidates entirely and
-- would miss the prime 2.  We instead enumerate every integer in (m, n]
-- and filter by primality, matching `spec_between_membership` and
-- `spec_between_via_upto` exactly: p ∈ between m n ↔ check p ∧ m < p ∧ p ≤ n.
#guard canonical.primepy.between 1 5 = [2, 3, 5]
#guard canonical.primepy.between 0 10 = [2, 3, 5, 7]
#guard canonical.primepy.between 10 20 = [11, 13, 17, 19]
#guard canonical.primepy.between 2 5 = [3, 5]
#guard canonical.primepy.between 14 30 = [17, 19, 23, 29]
#guard canonical.primepy.between 5 11 = [7, 11]
