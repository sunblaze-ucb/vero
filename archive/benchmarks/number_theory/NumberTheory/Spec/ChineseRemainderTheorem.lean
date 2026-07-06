import NumberTheory.Harness

/-!
# NumberTheory.Spec.ChineseRemainderTheorem

Specifications for Chinese Remainder Theorem utilities.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- Pin the output of extended_euclid at all five test inputs. -/
def spec_extended_euclid_concrete_pins (impl : RepoImpl) : Prop :=
  impl.numberTheory.extended_euclid 10 6 = (-1, 2) ∧
  impl.numberTheory.extended_euclid 7  5 = (-2, 3) ∧
  impl.numberTheory.extended_euclid 15 4 = (-1, 4) ∧
  impl.numberTheory.extended_euclid 0  5 = (0, 1)  ∧
  impl.numberTheory.extended_euclid 5  0 = (1, 0)

/-- At three non-degenerate test inputs, the Bezout identity a*x + b*y = gcd(a,b) holds for extended_euclid. -/
def spec_extended_euclid_bezout_at_pins (impl : RepoImpl) : Prop :=
  (let (x, y) := impl.numberTheory.extended_euclid 10 6;
   10 * x + 6 * y = impl.numberTheory.greatest_common_divisor 10 6) ∧
  (let (x, y) := impl.numberTheory.extended_euclid 7 5;
   7 * x + 5 * y = impl.numberTheory.greatest_common_divisor 7 5) ∧
  (let (x, y) := impl.numberTheory.extended_euclid 15 4;
   15 * x + 4 * y = impl.numberTheory.greatest_common_divisor 15 4)

/-- Pin the modular inverse at four test inputs. -/
def spec_invert_modulo_concrete_pins (impl : RepoImpl) : Prop :=
  impl.numberTheory.invert_modulo 3  11 = 4  ∧
  impl.numberTheory.invert_modulo 10 17 = 12 ∧
  impl.numberTheory.invert_modulo 7  13 = 2  ∧
  impl.numberTheory.invert_modulo 0  5  = 0

/-- For coprime inputs, (a * invert_modulo a n) % n = 1. -/
def spec_invert_modulo_round_trip (impl : RepoImpl) : Prop :=
  (3  * impl.numberTheory.invert_modulo 3  11) % 11 = 1 ∧
  (10 * impl.numberTheory.invert_modulo 10 17) % 17 = 1 ∧
  (7  * impl.numberTheory.invert_modulo 7  13) % 13 = 1

/-- Pin chinese_remainder_theorem at all four test inputs. -/
def spec_crt_concrete_pins (impl : RepoImpl) : Prop :=
  impl.numberTheory.chinese_remainder_theorem 5 1 7 3 = 31 ∧
  impl.numberTheory.chinese_remainder_theorem 6 1 4 3 = 14 ∧
  impl.numberTheory.chinese_remainder_theorem 3 2 5 3 = 8  ∧
  impl.numberTheory.chinese_remainder_theorem 5 0 7 0 = 0

/-- Pin chinese_remainder_theorem2 at all four test inputs. -/
def spec_crt2_concrete_pins (impl : RepoImpl) : Prop :=
  impl.numberTheory.chinese_remainder_theorem2 5 1 7 3 = 31 ∧
  impl.numberTheory.chinese_remainder_theorem2 6 1 4 3 = 14 ∧
  impl.numberTheory.chinese_remainder_theorem2 3 2 5 3 = 8  ∧
  impl.numberTheory.chinese_remainder_theorem2 5 0 7 0 = 0

/-- Both CRT implementations produce the same result at every test input. -/
def spec_crt_two_impls_agree (impl : RepoImpl) : Prop :=
  impl.numberTheory.chinese_remainder_theorem 5 1 7 3 = impl.numberTheory.chinese_remainder_theorem2 5 1 7 3 ∧
  impl.numberTheory.chinese_remainder_theorem 6 1 4 3 = impl.numberTheory.chinese_remainder_theorem2 6 1 4 3 ∧
  impl.numberTheory.chinese_remainder_theorem 3 2 5 3 = impl.numberTheory.chinese_remainder_theorem2 3 2 5 3 ∧
  impl.numberTheory.chinese_remainder_theorem 5 0 7 0 = impl.numberTheory.chinese_remainder_theorem2 5 0 7 0

/-- CRT defining property: for coprime moduli (n1,n2), result n satisfies
    n % n1 = r1, n % n2 = r2, 0 ≤ n, n < n1 * n2.
    Checked at the two coprime test inputs; (6,4) excluded as gcd(6,4)=2≠1. -/
def spec_crt_residue_at_pins (impl : RepoImpl) : Prop :=
  (let n := impl.numberTheory.chinese_remainder_theorem 5 1 7 3;
   n % 5 = 1 ∧ n % 7 = 3 ∧ 0 ≤ n ∧ n < 5 * 7) ∧
  (let n := impl.numberTheory.chinese_remainder_theorem 3 2 5 3;
   n % 3 = 2 ∧ n % 5 = 3 ∧ 0 ≤ n ∧ n < 3 * 5)

/-- Both extended GCD implementations (from different files) produce coefficients that
    yield the same Bezout combination for positive inputs. -/
def spec_extended_euclid_implementations_agree (impl : RepoImpl) : Prop :=
  ∀ (a b : Int), a > 0 → b > 0 →
    let (x1, y1) := impl.numberTheory.extended_euclidean_algorithm a b
    let (x2, y2) := impl.numberTheory.extended_euclid a b
    a * x1 + b * y1 = a * x2 + b * y2

/-- The CRT-local extended Euclidean algorithm returns coefficients satisfying Bezout's identity. -/
def spec_extended_euclid_bezout_identity (impl : RepoImpl) : Prop :=
  ∀ (a b : Int), a > 0 → b > 0 →
    let (x, y) := impl.numberTheory.extended_euclid a b
    a * x + b * y = impl.numberTheory.greatest_common_divisor a b

/-- The CRT result satisfies the first congruence: result mod n1 = r1. -/
def spec_crt_satisfies_first_congruence (impl : RepoImpl) : Prop :=
  ∀ (n1 r1 n2 r2 : Int), n1 > 0 → n2 > 0 →
    impl.numberTheory.greatest_common_divisor n1 n2 = 1 →
    0 ≤ r1 → r1 < n1 → 0 ≤ r2 → r2 < n2 →
    impl.numberTheory.chinese_remainder_theorem n1 r1 n2 r2 % n1 = r1

/-- The CRT result satisfies the second congruence: result mod n2 = r2. -/
def spec_crt_satisfies_second_congruence (impl : RepoImpl) : Prop :=
  ∀ (n1 r1 n2 r2 : Int), n1 > 0 → n2 > 0 →
    impl.numberTheory.greatest_common_divisor n1 n2 = 1 →
    0 ≤ r1 → r1 < n1 → 0 ≤ r2 → r2 < n2 →
    impl.numberTheory.chinese_remainder_theorem n1 r1 n2 r2 % n2 = r2

/-- Both CRT implementations (one using extended_euclid, the other using invert_modulo)
    produce the same result for valid coprime inputs. -/
def spec_crt_implementations_agree (impl : RepoImpl) : Prop :=
  ∀ (n1 r1 n2 r2 : Int), n1 > 0 → n2 > 0 →
    impl.numberTheory.greatest_common_divisor n1 n2 = 1 →
    0 ≤ r1 → r1 < n1 → 0 ≤ r2 → r2 < n2 →
    impl.numberTheory.chinese_remainder_theorem n1 r1 n2 r2 =
      impl.numberTheory.chinese_remainder_theorem2 n1 r1 n2 r2

/-- The CRT result lies in the range [0, n1*n2) for valid coprime inputs. -/
def spec_crt_range (impl : RepoImpl) : Prop :=
  ∀ (n1 r1 n2 r2 : Int), n1 > 0 → n2 > 0 →
    impl.numberTheory.greatest_common_divisor n1 n2 = 1 →
    0 ≤ r1 → r1 < n1 → 0 ≤ r2 → r2 < n2 →
    let result := impl.numberTheory.chinese_remainder_theorem n1 r1 n2 r2
    0 ≤ result ∧ result < n1 * n2

/-- invert_modulo a n returns b such that (a*b) ≡ 1 (mod n) when gcd(a, n) = 1 and n > 1. -/
def spec_invert_modulo_is_inverse (impl : RepoImpl) : Prop :=
  ∀ (a n : Int), n > 1 →
    impl.numberTheory.greatest_common_divisor a n = 1 →
    (a * impl.numberTheory.invert_modulo a n) % n = 1
