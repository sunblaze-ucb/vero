import DedekindReals.Impl.Cut
import DedekindReals.Impl.Additive

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# DedekindReals.Impl.DecOrder

Logical consequences of decidable order for Dedekind cuts, translated from
the Coq `DecOrder` module.

DO NOT MODIFY types or signatures -- these are the fixed vocabulary.
This module has no assigned scored APIs.
-/

-- !benchmark @start global_aux
-- !benchmark @end global_aux

namespace DedekindReals

-- Types

inductive BoundSearchTerminates : R → Prop where
  | xIsNegative {x : R} : x.upper 0 → BoundSearchTerminates x
  | xStepSearch {x : R} :
      BoundSearchTerminates (Rminus x (R_of_Q 1)) →
        BoundSearchTerminates x

-- Pure spec helpers.

def LPO : Prop :=
  ∀ un : Nat → Bool, (∃ n : Nat, un n = true) ∨ (∀ n : Nat, un n = false)

def LPO_epsilon : Prop :=
  LPO → ∀ un : Nat → Bool, (∃ n : Nat, un n = true) ∨ (∀ n : Nat, un n = false)

def LPO_dec : Prop :=
  ∀ P : Nat → Prop, (∀ n : Nat, P n ∨ ¬ P n) → LPO →
    (∃ n : Nat, P n) ∨ (∀ n : Nat, ¬ P n)

def sig_not_dec_T : Prop :=
  ∀ P : Prop, ¬¬P ∨ ¬P

def sig_or_not_dec_T : Prop :=
  ∀ P Q : Prop, (¬P ∨ ¬Q) → ¬P ∨ ¬Q

def sig_not_implies_sig_or_not : Prop :=
  sig_not_dec_T → sig_or_not_dec_T

def sig_located : Prop :=
  sig_or_not_dec_T → ∀ (x : R) (q r : Rat), q < r → x.lower q ∨ x.upper r

def upper_bound_epsilon : Prop :=
  sig_or_not_dec_T → ∀ x : R, ∃ q : Rat, x.upper q

def lower_bound_epsilon : Prop :=
  sig_or_not_dec_T → ∀ x : R, ∃ q : Rat, x.lower q

-- Pure API helpers.

def fix_bound_epsilon : Prop :=
  ∀ (x : R), BoundSearchTerminates x → sig_or_not_dec_T → ∃ q : Rat, x.upper q

end DedekindReals
