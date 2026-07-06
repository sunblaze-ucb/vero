-- !benchmark @start imports
-- !benchmark @end imports

/-!
# NumberTheory.Impl.GcdOfNNumbers

GCD of N numbers via prime factorization.

Source: `maths/gcd_of_n_numbers.py` from TheAlgorithms/Python.
Uses a `Counter` (list of prime-factor → exponent pairs) to factorize
each number, then intersects the factor maps to find the common factors.

Note: The generic `α` from benchmark.json is simplified to the concrete
`Counter := List (Int × Nat)` type for a clean Lean translation.
   used polymorphic α but concrete implementation is Counter = List (Int × Nat)

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
Implement only the function bodies.
-/

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- ── Types (no markers — fixed vocabulary) ────────────────────────────

/-- A prime factorization represented as a list of (prime, exponent) pairs. -/
abbrev Counter := List (Int × Nat)

namespace NT

-- ── API signatures (no markers — fixed vocabulary) ────────────────────

abbrev GetFactorsSig                := Int → Counter → Int → Counter
abbrev GetGreatestCommonDivisorSig  := List Int → Int

end NT

-- ── Implementations ───────────────────────────────────────────────────

-- !benchmark @start code_aux def=get_factors
/-- Insert or increment the count of `factor` in `acc`. -/
private def counterInsert (factor : Int) (acc : Counter) : Counter :=
  if acc.any (fun p => p.1 == factor) then
    acc.map (fun (p, e) => if p == factor then (p, e + 1) else (p, e))
  else
    acc ++ [(factor, 1)]

/-- Intersect two Counter maps: keep common keys with the minimum exponent. -/
private def counterIntersect (c1 c2 : Counter) : Counter :=
  c1.filterMap fun (p, e1) =>
    match c2.find? (fun q => q.1 == p) with
    | none         => none
    | some (_, e2) => some (p, min e1 e2)
-- !benchmark @end code_aux def=get_factors

partial def NT.get_factors : NT.GetFactorsSig :=
-- !benchmark @start code def=get_factors
  -- @review human: termination via n decreasing and factor increasing; partial over Int
  fun n factors factor =>
    if n == 1 then
      counterInsert 1 factors
    else if n == factor then
      counterInsert factor factors
    else if n % factor != 0 then
      NT.get_factors n factors (factor + 1)
    else
      NT.get_factors (n / factor) (counterInsert factor factors) factor
-- !benchmark @end code def=get_factors

-- !benchmark @start code_aux def=get_greatest_common_divisor
/-- Multiply out all (prime, exponent) pairs: product of prime^exponent. -/
private def counterProduct (c : Counter) : Int :=
  c.foldl (fun acc (p, e) => acc * Int.pow p e) 1
-- !benchmark @end code_aux def=get_greatest_common_divisor

def NT.get_greatest_common_divisor : NT.GetGreatestCommonDivisorSig :=
-- !benchmark @start code def=get_greatest_common_divisor
  fun numbers =>
    match numbers with
    | []      => 0
    | [n]     => n
    | n :: ns =>
      let initFactors := NT.get_factors n [] 2
      let common := ns.foldl (fun acc m =>
        counterIntersect acc (NT.get_factors m [] 2)) initFactors
      counterProduct common
-- !benchmark @end code def=get_greatest_common_divisor
