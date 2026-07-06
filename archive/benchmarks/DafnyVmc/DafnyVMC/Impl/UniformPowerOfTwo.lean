import DafnyVMC.Impl.Monad

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# DafnyVMC.Impl.UniformPowerOfTwo

External RNG primitive for the uniform-power-of-two distribution.
Corresponds to `src/Distributions/UniformPowerOfTwo/Interface.dfy`.

`uniformPowerOfTwoSample n h` axiomatises a sampler that draws from
`[0, 2^k)` where `k = ⌊log₂ n⌋` (i.e., `2^k ≤ n < 2^(k+1)`).
The Dafny source declares this as a trait interface method with no body;
it is treated as an opaque primitive here.

DO NOT MODIFY types — these are the fixed vocabulary.
-/

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- ── External axiom (DO NOT MODIFY) ────────────────────────────────


/-- External RNG primitive: samples a natural number uniformly from
    `[0, 2^k)` where `k = ⌊log₂ n⌋`.  The requirement `n ≥ 1` ensures
    `k` is well-defined.  Corresponds to
    `UniformPowerOfTwo.Interface.Trait.UniformPowerOfTwoSample`.
    Declared as an interface method in Dafny (no implementation);
    axiomatised here as an opaque Hurd computation. -/
opaque uniformPowerOfTwoSample (n : Nat) (h : n ≥ 1) : Hurd Nat
