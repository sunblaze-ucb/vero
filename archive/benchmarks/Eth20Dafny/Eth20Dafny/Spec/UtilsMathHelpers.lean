import Eth20Dafny.Harness

/-!
# Eth20Dafny.Spec.UtilsMathHelpers

Specifications for `MathHelpers` utilities.
-/

def spec_getNextPow2isPower2 (impl : RepoImpl) : Prop :=
  ∀ (n : Nat), ∃ k : Nat, impl.eth2Dafny.get_next_power_of_two n = Eth20Dafny.power2 k

def spec_getPrevPow2isPower2 (impl : RepoImpl) : Prop :=
  ∀ (n : Nat), 0 < n → ∃ k : Nat, impl.eth2Dafny.get_prev_power_of_two n = Eth20Dafny.power2 k

def spec_getNextPow2isIdempotent (impl : RepoImpl) : Prop :=
  ∀ (n : Nat), impl.eth2Dafny.get_next_power_of_two (impl.eth2Dafny.get_next_power_of_two n) = impl.eth2Dafny.get_next_power_of_two n

def spec_getNextPow2LowerBound (impl : RepoImpl) : Prop :=
  ∀ (n : Nat), n ≤ impl.eth2Dafny.get_next_power_of_two n

def spec_nextPow2IsPow2 (impl : RepoImpl) : Prop :=
  ∀ (n : Nat), Eth20Dafny.isPowerOf2 (impl.eth2Dafny.get_next_power_of_two n)
