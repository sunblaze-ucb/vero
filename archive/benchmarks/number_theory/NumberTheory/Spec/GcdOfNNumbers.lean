import NumberTheory.Harness

/-!
# NumberTheory.Spec.GcdOfNNumbers

Specifications for GCD of N numbers operations.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- Multiply out all (prime, exponent) pairs in a Counter: ∏ p^e. -/
def spec_helper_counter_product (c : List (Int × Nat)) : Int :=
  c.foldl (fun acc pe => acc * Int.pow pe.1 pe.2) 1

/-- Every element in a list is strictly positive. -/
def spec_helper_all_positive : List Int → Prop
  | [] => True
  | x :: xs => x > 0 ∧ spec_helper_all_positive xs

/-- `d` divides every element in a list. -/
def spec_helper_divides_all (d : Int) : List Int → Prop
  | [] => True
  | x :: xs => x % d = 0 ∧ spec_helper_divides_all d xs

/-- Pin the prime factorization output of get_factors at five test inputs. -/
def spec_get_factors_concrete (impl : RepoImpl) : Prop :=
  impl.numberTheory.get_factors 45   [] 2 = [(3, 2), (5, 1)]                  ∧
  impl.numberTheory.get_factors 2520 [] 2 = [(2, 3), (3, 2), (5, 1), (7, 1)] ∧
  impl.numberTheory.get_factors 23   [] 2 = [(23, 1)]                         ∧
  impl.numberTheory.get_factors 12   [] 2 = [(2, 2), (3, 1)]                  ∧
  impl.numberTheory.get_factors 100  [] 2 = [(2, 2), (5, 2)]

/-- For every positive input n, the product ∏ p^e over get_factors n [] 2 equals n. -/
def spec_get_factors_product_round_trip (impl : RepoImpl) : Prop :=
  ∀ n : Int, n > 0 →
    spec_helper_counter_product (impl.numberTheory.get_factors n [] 2) = n

/-- The GCD of an empty list is 0. -/
def spec_get_gcd_empty (impl : RepoImpl) : Prop :=
  impl.numberTheory.get_greatest_common_divisor [] = 0

/-- The GCD of a singleton list [n] is n. -/
def spec_get_gcd_singleton (impl : RepoImpl) : Prop :=
  ∀ n : Int, impl.numberTheory.get_greatest_common_divisor [n] = n

/-- On two positive inputs, the n-ary GCD agrees with the binary GCD API. -/
def spec_get_gcd_pair_agrees_with_binary_gcd (impl : RepoImpl) : Prop :=
  ∀ a b : Int, a > 0 → b > 0 →
    impl.numberTheory.get_greatest_common_divisor [a, b] =
      impl.numberTheory.greatest_common_divisor a b

/-- Pin the GCD-of-N-numbers output at the five test inputs. -/
def spec_get_gcd_concrete_pins (impl : RepoImpl) : Prop :=
  impl.numberTheory.get_greatest_common_divisor [18, 45]                         = 9  ∧
  impl.numberTheory.get_greatest_common_divisor [23, 37]                         = 1  ∧
  impl.numberTheory.get_greatest_common_divisor [2520, 8350]                     = 10 ∧
  impl.numberTheory.get_greatest_common_divisor [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] = 1  ∧
  impl.numberTheory.get_greatest_common_divisor [12, 18, 24]                     = 6

/-- For every nonempty positive list, the returned value is a common divisor. -/
def spec_get_gcd_divides_all (impl : RepoImpl) : Prop :=
  ∀ xs : List Int, xs ≠ [] → spec_helper_all_positive xs →
    spec_helper_divides_all (impl.numberTheory.get_greatest_common_divisor xs) xs

/-- For every nonempty positive list, the returned value is the greatest common divisor. -/
def spec_get_gcd_greatest (impl : RepoImpl) : Prop :=
  ∀ (xs : List Int) (d : Int), xs ≠ [] → spec_helper_all_positive xs → d > 0 →
    spec_helper_divides_all d xs →
      d ≤ impl.numberTheory.get_greatest_common_divisor xs
