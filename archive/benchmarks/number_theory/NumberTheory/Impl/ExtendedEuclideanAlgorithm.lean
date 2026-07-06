-- !benchmark @start imports
-- !benchmark @end imports

/-!
# NumberTheory.Impl.ExtendedEuclideanAlgorithm

Extended Euclidean Algorithm (Bezout's Identity).

Source: `maths/extended_euclidean_algorithm.py` from TheAlgorithms/Python.
Finds coefficients (s, t) such that `a * s + b * t = gcd(a, b)`.

The Python implementation is iterative. This Lean translation uses a
tail-recursive helper that carries the running state.

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
Implement only the function bodies.
-/

-- !benchmark @start global_aux
-- !benchmark @end global_aux

namespace NT

-- ── API signatures (no markers — fixed vocabulary) ────────────────────

abbrev ExtendedEuclideanAlgorithmSig := Int → Int → Int × Int

end NT

-- ── Implementations ───────────────────────────────────────────────────

-- !benchmark @start code_aux def=extended_euclidean_algorithm
/-- Tail-recursive extended-GCD state carrier.
    Returns (old_coeff_a, old_coeff_b) when rem = 0. -/
private partial def eexIter
    (old_rem rem old_ca ca old_cb cb : Int) : Int × Int :=
  if rem == 0 then (old_ca, old_cb)
  else
    -- Use Int.fdiv (floor division) to match Python's // operator
    let q := Int.fdiv old_rem rem
    eexIter rem (old_rem - q * rem) ca (old_ca - q * ca) cb (old_cb - q * cb)
-- !benchmark @end code_aux def=extended_euclidean_algorithm

def NT.extended_euclidean_algorithm : NT.ExtendedEuclideanAlgorithmSig :=
-- !benchmark @start code def=extended_euclidean_algorithm
  -- @review human: termination via |rem| decreasing (Euclidean algorithm); uses partial eexIter
  fun a b =>
    -- Python base cases
    if Int.natAbs a == 1 then (a, 0)
    else if Int.natAbs b == 1 then (0, b)
    else
      let (oca, ocb) := eexIter a b 1 0 0 1
      -- Sign correction for negative inputs (matches Python behaviour)
      let s := if a < 0 then -oca else oca
      let t := if b < 0 then -ocb else ocb
      (s, t)
-- !benchmark @end code def=extended_euclidean_algorithm
