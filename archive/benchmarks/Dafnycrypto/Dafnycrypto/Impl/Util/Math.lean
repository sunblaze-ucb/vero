import Dafnycrypto.Impl.Util.Option

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Dafnycrypto.Impl.Util.Math

Mathematical utilities: vector arithmetic, fast exponentiation, modular exponentiation,
and the extended Euclidean algorithm with modular inverse. Translated from the Dafny
`MathUtils` module.

Types and signatures are fixed vocabulary — DO NOT MODIFY.
Implement only the function bodies.
-/

-- ── Spec helpers (fully defined, not LLM tasks) ────────────────────────────────

/-- A natural number n is prime if n > 1 and every 1 ≤ a < n is coprime to n. -/
def DafnyCrypto.IsPrime (n : Nat) : Prop :=
  n > 1 ∧ ∀ a : Nat, 1 ≤ a → a < n → Nat.gcd a n = 1

/-- Multiplication of naturals is associative. -/
theorem DafnyCrypto.mulAssoc (x y z : Nat) : x * y * z = x * (y * z) :=
  Nat.mul_assoc x y z

/-- Multiplication of naturals is commutative. -/
theorem DafnyCrypto.mulComm (x y : Nat) : x * y = y * x :=
  Nat.mul_comm x y

-- ── API helpers (fully defined, not LLM tasks) ─────────────────────────────────

/-- Absolute value of an integer as a natural number. -/
def DafnyCrypto.abs (x : Int) : Nat := x.natAbs

/-- Sum all integers in a list. -/
def DafnyCrypto.vecSum (vec : List Int) : Int := vec.foldl (· + ·) 0

-- ── API signatures (DO NOT MODIFY) ────────────────────────────────────────────

namespace DafnyCrypto

abbrev VecMulSig     := List Int → List Int → List Int
abbrev VecAddSig     := List Int → List Int → List Int
abbrev PowSig        := Nat → Nat → Nat
abbrev PowNSig       := Nat → Nat → List Nat
abbrev ModPowSig     := Nat → Nat → Nat → Nat
abbrev GcdExtendedSig := Nat → Nat → Nat × Int × Int
abbrev InverseSig    := Nat → Nat → Option Nat

end DafnyCrypto

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- ── Implementation stubs (LLM task) ───────────────────────────────────────────

-- !benchmark @start code_aux def=vecMul
-- !benchmark @end code_aux def=vecMul

def DafnyCrypto.vecMul : DafnyCrypto.VecMulSig :=
-- !benchmark @start code def=vecMul
  fun left right => List.zipWith (· * ·) left right
-- !benchmark @end code def=vecMul

-- !benchmark @start code_aux def=vecAdd
-- !benchmark @end code_aux def=vecAdd

def DafnyCrypto.vecAdd : DafnyCrypto.VecAddSig :=
-- !benchmark @start code def=vecAdd
  fun left right => List.zipWith (· + ·) left right
-- !benchmark @end code def=vecAdd

-- !benchmark @start code_aux def=pow
-- !benchmark @end code_aux def=pow

def DafnyCrypto.pow : DafnyCrypto.PowSig :=
-- !benchmark @start code def=pow
  fun n k => n ^ k
-- !benchmark @end code def=pow

-- lemmaPow2 placed after pow to satisfy forward-reference: it mentions DafnyCrypto.pow.

/-- `pow 2 k` is strictly positive for all k. -/
theorem DafnyCrypto.lemmaPow2 (k : Nat) : DafnyCrypto.pow 2 k > 0 := by
  simp only [DafnyCrypto.pow]
  apply Nat.one_le_pow
  decide

-- !benchmark @start code_aux def=powN
-- !benchmark @end code_aux def=powN

def DafnyCrypto.powN : DafnyCrypto.PowNSig :=
-- !benchmark @start code def=powN
  fun x n => List.range n |>.map (fun i => x ^ i)
-- !benchmark @end code def=powN

-- !benchmark @start code_aux def=modPow
-- !benchmark @end code_aux def=modPow

def DafnyCrypto.modPow : DafnyCrypto.ModPowSig :=
-- !benchmark @start code def=modPow
  fun n k m => (n ^ k) % m
-- !benchmark @end code def=modPow

-- !benchmark @start code_aux def=gcdExtended
/-- Recursive core of the extended Euclidean algorithm. Returns (gcd, x, y)
    satisfying a*x + b*y = gcd (Bezout identity). -/
private def gcdExtended_go (n : Nat) (b : Nat) : Nat × Int × Int :=
  match n with
  | 0 => (b, 0, 1)
  | (a + 1) =>
    let (g, x, y) := gcdExtended_go (b % (a + 1)) (a + 1)
    (g, y - ↑(b / (a + 1)) * x, x)
termination_by n
decreasing_by exact Nat.mod_lt b (Nat.succ_pos a)
-- !benchmark @end code_aux def=gcdExtended

def DafnyCrypto.gcdExtended : DafnyCrypto.GcdExtendedSig :=
-- !benchmark @start code def=gcdExtended
  gcdExtended_go
-- !benchmark @end code def=gcdExtended

-- !benchmark @start code_aux def=inverse
-- !benchmark @end code_aux def=inverse

def DafnyCrypto.inverse : DafnyCrypto.InverseSig :=
-- !benchmark @start code def=inverse
  fun a n =>
    let (gcd, x, _) := gcdExtended_go a n
    if gcd > 1 then none
    else if x ≥ 0 then some x.toNat
    else some (x + ↑n).toNat
-- !benchmark @end code def=inverse
