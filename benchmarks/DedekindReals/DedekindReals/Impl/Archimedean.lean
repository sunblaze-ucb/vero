import DedekindReals.Impl.Cut

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# DedekindReals.Impl.Archimedean

Frozen Archimedean approximation vocabulary translated from the Coq
`Archimedean` module.

DO NOT MODIFY types or signatures -- these are the fixed vocabulary.
This module has no assigned scored APIs.
-/

-- !benchmark @start global_aux
-- !benchmark @end global_aux

namespace DedekindReals

-- Pure spec helpers.

def straddle (x : R) (q : Rat) : Prop :=
  ∃ l u : Rat, x.lower l ∧ x.upper u ∧ u - l < q

def straddle_monotone : Prop :=
  ∀ (x : R) (q r : Rat), q < r → straddle x q → straddle x r

def propSwitch : Prop :=
  ∀ (L U : Nat → Prop) (k : Nat),
    (∀ n : Nat, L n ∨ U (n + 1)) →
      L 0 →
        U (k + 2) →
          ∃ p : Nat, L p ∧ U (p + 2)

end DedekindReals
