import ArithmeticV2.Impl.Power
import ArithmeticV2.Impl.Power2

/-!
# ArithmeticV2.Impl.Logarithm

Integer logarithm helper vocabulary translated from Verus `logarithm.rs`. This
module has no scored executable APIs; the definitions here are frozen
vocabulary used by translated specifications.
-/


namespace ArithmeticV2

/--
Fuel-bounded recursive definition of the integer logarithm. It is only
meaningful when `base > 1` and `pow >= 0`.
-/
def logFuel (base : Int) : Int → Nat → Int
  | _pow, 0 => 0
  | pow, fuel + 1 =>
      if pow < base ∨ pow / base >= pow ∨ pow / base < 0 then 0
      else 1 + logFuel base (pow / base) fuel

/--
This function recursively defines the integer logarithm. It's only meaningful
when the base of the logarithm `base` is greater than 1, and when the value
whose logarithm is taken, `pow`, is non-negative.
-/
def log (base pow : Int) : Int :=
  logFuel base pow (pow.natAbs + 1)

end ArithmeticV2
