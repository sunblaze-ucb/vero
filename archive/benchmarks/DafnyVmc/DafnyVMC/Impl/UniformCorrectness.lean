import DafnyVMC.Impl.UniformModel

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# DafnyVMC.Impl.UniformCorrectness

Vocabulary helper `sampleEquals` for the uniform correctness specs.
Corresponds to vocabulary used in `src/Distributions/Uniform/Correctness.dfy`.

- `sampleEquals n i hn hi` is the event (measurable subset of `Bitstream`)
  on which `sample n hn` returns value `i`.

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
-/

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- ── Vocabulary (DO NOT MODIFY) ────────────────────────────────────────

/-- The event that `sample n hn` returns value `i` on a bitstream.
    A `Set Bitstream` used in uniformity correctness specifications.
    Corresponds to vocabulary in `Uniform.Correctness`. -/
def sampleEquals (n i : Nat) (hn : n > 0) (_ : i < n) : Set Bitstream :=
  {s | (sample n hn s).value = i}
