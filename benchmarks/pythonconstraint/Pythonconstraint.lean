import Pythonconstraint.Impl.Csp
import Pythonconstraint.Bundle
import Pythonconstraint.Harness
import Pythonconstraint.Spec.Csp
import Pythonconstraint.Test

/-!
# Pythonconstraint

Root import hub: finite-domain constraint-satisfaction solving, ported from the
`python-constraint` library (`constraint/__init__.py`, Gustavo Niemeyer, BSD;
v1.4.0). A CSP is a list of variables (indices `0 … n-1`), each with a finite
`Nat` domain, plus a list of `Constraint`s; the solver enumerates every value
assignment satisfying all constraints.

CSP core (`Impl/Csp`, `Spec/Csp`): `getSolutions` (the full solution set),
`getSolution` (one solution or `none`), `solutionCount` (how many), and `holds`
(the frozen constraint evaluator). The crown properties are **soundness** (every
returned assignment respects the domains and satisfies every constraint) and
**completeness** (every domain-respecting assignment satisfying all constraints
appears in `getSolutions` — the returned set is exactly the full model set,
forbidding an incomplete solver), fused into the two-sided
`spec_solutions_eq_modelset`. Constraint semantics are anchored to frozen
predicates: `AllDifferent` ⟺ pairwise-distinct values (injectivity), `ExactSum k`
⟺ the values sum to `k`.

Behaviour is pinned by `Spec/Csp.lean`.
-/
