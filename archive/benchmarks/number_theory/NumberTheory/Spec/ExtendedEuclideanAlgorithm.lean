import NumberTheory.Harness

/-!
# NumberTheory.Spec.ExtendedEuclideanAlgorithm

Specifications for the extended Euclidean algorithm.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- Pin the output of extended_euclidean_algorithm at all nine test inputs. -/
def spec_eea_concrete_pins (impl : RepoImpl) : Prop :=
  impl.numberTheory.extended_euclidean_algorithm 1    24             = (1, 0)    ∧
  impl.numberTheory.extended_euclidean_algorithm 8    14             = (2, -1)   ∧
  impl.numberTheory.extended_euclidean_algorithm 240  46             = (-9, 47)  ∧
  impl.numberTheory.extended_euclidean_algorithm 1    (-4)           = (1, 0)    ∧
  impl.numberTheory.extended_euclidean_algorithm (-2) (-4)           = (-1, 0)   ∧
  impl.numberTheory.extended_euclidean_algorithm 0    (-4)           = (0, -1)   ∧
  impl.numberTheory.extended_euclidean_algorithm 2    0              = (1, 0)    ∧
  impl.numberTheory.extended_euclidean_algorithm 123456789 987654321 = (-8, 1)   ∧
  impl.numberTheory.extended_euclidean_algorithm (-123) (-456)       = (63, -17)

/-- At positive test inputs, the Bezout identity a*s + b*t = gcd(a,b) holds. -/
def spec_eea_bezout_at_pins (impl : RepoImpl) : Prop :=
  (let (s, t) := impl.numberTheory.extended_euclidean_algorithm 8 14;
   8 * s + 14 * t = impl.numberTheory.greatest_common_divisor 8 14) ∧
  (let (s, t) := impl.numberTheory.extended_euclidean_algorithm 240 46;
   240 * s + 46 * t = impl.numberTheory.greatest_common_divisor 240 46) ∧
  (let (s, t) := impl.numberTheory.extended_euclidean_algorithm 2 0;
   2 * s + 0 * t = impl.numberTheory.greatest_common_divisor 2 0) ∧
  (let (s, t) := impl.numberTheory.extended_euclidean_algorithm 123456789 987654321;
   123456789 * s + 987654321 * t = impl.numberTheory.greatest_common_divisor 123456789 987654321)

/-- The extended Euclidean algorithm returns coefficients (x, y) satisfying Bezout's identity:
    a*x + b*y = gcd(a, b), provided (a, b) ≠ (0, 0). -/
def spec_bezout_identity (impl : RepoImpl) : Prop :=
  ∀ (a b : Int), a ≠ 0 ∨ b ≠ 0 →
    let (x, y) := impl.numberTheory.extended_euclidean_algorithm a b
    a * x + b * y = impl.numberTheory.greatest_common_divisor a b
