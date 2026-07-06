import Portion.Impl.Algebra
import Portion.Bundle
import Portion.Harness
import Portion.Spec.Algebra
import Portion.Test

/-!
# Portion

Root import hub for the interval set-algebra benchmark.

The benchmark is the full Boolean algebra of subsets of `Int` that change
membership at finitely many points: `union` (`|`), `intersection` (`&`),
`complement` (`~`), and `difference` (`-`), each returning the unique canonical
representation of the corresponding point-set operation, plus `contains` and
`isEmpty` observers.

A set is `IntervalSet := { neg : Bool, cuts : List Int }`: `neg` is the
membership at `-∞` and `cuts` are the points where membership toggles. The
canonical form has `cuts` strictly increasing. Behaviour is pinned by
Spec/Algebra.lean against a frozen point-membership predicate.
-/
