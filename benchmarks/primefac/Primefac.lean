import Primefac.Impl.Factor
import Primefac.Bundle
import Primefac.Harness
import Primefac.Spec.Factor
import Primefac.Test

/-!
# Primefac

Root import hub for the integer-factorization benchmark over `Nat`.

Three APIs: `isprime n : Bool` (primality test), `iterprod xs : Nat` (running
product of a list), and `primefac n : List Nat` (the prime factorization of `n`
as a nondecreasing list). `primefac 0` and `primefac 1` are `[]`.

Specs pin `isprime` to the divisibility characterization of primality and pin
`primefac` to the unique sorted prime list whose product is `n`, plus the deep
structural laws (multiplicativity, per-prime valuation, squarefree shape,
least prime factor). Behaviour is fixed by `Spec/Factor.lean`.
-/
