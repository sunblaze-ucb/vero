import DafnyVMC.Impl.Independence
import DafnyVMC.Impl.Measures

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# DafnyVMC.Impl.UniformModel

Uniform distribution sampler for `[0, n)` and interval sampler for `[a, b)`.
Corresponds to `src/Distributions/Uniform/Model.dfy`.

- `sample n h` is axiomatised as a ghost function with four properties:
  (weak) independence, measure-preservation, value bound, and uniformity.
  Each postcondition of Dafny's `Sample` becomes a separate `axiom`.
- `intervalSample a b h` samples from `[a, b)` by shifting a
  `sample (b - a).toNat` result by `a`.

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
Implement only the function bodies.
-/

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- ── Axiomatised uniform sampler (DO NOT MODIFY) ────────────────────────────────


/-- Axiomatised uniform sampler on `[0, n)`.
    Corresponds to Dafny's `ghost function {:axiom} Sample(n: nat)`.
    The four postconditions are each stated as separate axioms below. -/
opaque sample (n : Nat) (h : n > 0) : Hurd Nat

/-- `sample n h` is a (weakly) independent Hurd function.
    Corresponds to the first `ensures` clause of Dafny's `Sample`. -/
axiom sample_isIndepFunction (n : Nat) (h : n > 0) :
    isIndepFunction (sample n h)

/-- The rest-projection of `sample n h` is measure-preserving on `(Bitstream, prob)`.
    Corresponds to the second `ensures` clause of Dafny's `Sample`. -/
axiom sample_isMeasurePreserving (n : Nat) (h : n > 0) :
    MeasureTheory.MeasurePreserving (fun s => (sample n h s).rest) prob prob

/-- The value produced by `sample n h s` lies strictly below `n`.
    Corresponds to the third `ensures` clause of Dafny's `Sample`. -/
axiom sample_bound (n : Nat) (h : n > 0) (s : Bitstream) :
    (sample n h s).value < n

/-- Each value `i < n` has probability exactly `1/n` under `sample n h`.
    Corresponds to the fourth `ensures` clause of Dafny's `Sample`. -/
axiom sample_uniform (n : Nat) (h : n > 0) (i : Nat) (hi : i < n) :
    prob {s | (sample n h s).value = i} = (1 : ENNReal) / n

-- ── Interval sampler (reference implementation — LLM task) ────────────────────

-- !benchmark @start code_aux def=intervalSample
-- !benchmark @end code_aux def=intervalSample

def intervalSample (a b : Int) (h : a < b) : Hurd Int :=
-- !benchmark @start code def=intervalSample
  map (sample (b - a).toNat (by omega)) (· + a)
-- !benchmark @end code def=intervalSample
