-- !benchmark @start imports
-- !benchmark @end imports

/-!
# NumberTheory.Impl.ChineseRemainderTheorem

Chinese Remainder Theorem utilities.

Source: `maths/chinese_remainder_theorem.py` from TheAlgorithms/Python.
Provides:
- `extended_euclid`: recursive extended GCD returning Bezout coefficients.
- `chinese_remainder_theorem`: CRT using `extended_euclid`.
- `invert_modulo`: modular inverse via `extended_euclid`.
- `chinese_remainder_theorem2`: CRT using `invert_modulo`.

Note: `extended_euclid` here is a different (recursive) implementation
from `extended_euclidean_algorithm` in the ExtendedEuclideanAlgorithm
module. They compute the same mathematical object but differ in sign
conventions and structure.

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
Implement only the function bodies.
-/

-- !benchmark @start global_aux
-- !benchmark @end global_aux

namespace NT

-- ── API signatures (no markers — fixed vocabulary) ────────────────────

abbrev ExtendedEuclidSig            := Int → Int → Int × Int
abbrev ChineseRemainderTheoremSig   := Int → Int → Int → Int → Int
abbrev InvertModuloSig              := Int → Int → Int
abbrev ChineseRemainderTheorem2Sig  := Int → Int → Int → Int → Int

end NT

-- ── Implementations ───────────────────────────────────────────────────

-- !benchmark @start code_aux def=extended_euclid
-- !benchmark @end code_aux def=extended_euclid

partial def NT.extended_euclid : NT.ExtendedEuclidSig :=
-- !benchmark @start code def=extended_euclid
  -- @review human: termination via |b| strictly decreasing (Euclidean); partial over Int
  fun a b =>
    if b == 0 then (1, 0)
    else
      let (x, y) := NT.extended_euclid b (a % b)
      let k := a / b
      (y, x - k * y)
-- !benchmark @end code def=extended_euclid

-- !benchmark @start code_aux def=chinese_remainder_theorem
-- !benchmark @end code_aux def=chinese_remainder_theorem

def NT.chinese_remainder_theorem : NT.ChineseRemainderTheoremSig :=
-- !benchmark @start code def=chinese_remainder_theorem
  fun n1 r1 n2 r2 =>
    let (x, y) := NT.extended_euclid n1 n2
    let m := n1 * n2
    let n := r2 * x * n1 + r1 * y * n2
    (n % m + m) % m
-- !benchmark @end code def=chinese_remainder_theorem

-- !benchmark @start code_aux def=invert_modulo
-- !benchmark @end code_aux def=invert_modulo

def NT.invert_modulo : NT.InvertModuloSig :=
-- !benchmark @start code def=invert_modulo
  fun a n =>
    let (b, _) := NT.extended_euclid a n
    if b < 0 then (b % n + n) % n else b
-- !benchmark @end code def=invert_modulo

-- !benchmark @start code_aux def=chinese_remainder_theorem2
-- !benchmark @end code_aux def=chinese_remainder_theorem2

def NT.chinese_remainder_theorem2 : NT.ChineseRemainderTheorem2Sig :=
-- !benchmark @start code def=chinese_remainder_theorem2
  fun n1 r1 n2 r2 =>
    let x := NT.invert_modulo n1 n2
    let y := NT.invert_modulo n2 n1
    let m := n1 * n2
    let n := r2 * x * n1 + r1 * y * n2
    (n % m + m) % m
-- !benchmark @end code def=chinese_remainder_theorem2
