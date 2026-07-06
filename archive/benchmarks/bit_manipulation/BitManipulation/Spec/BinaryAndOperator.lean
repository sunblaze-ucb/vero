import BitManipulation.Harness
import BitManipulation.Spec.Aux

/-!
# BitManipulation.Spec.BinaryAndOperator

Specifications for the `binary_and` API, plus shared string-parsing helpers
used by multiple spec modules.

DO NOT MODIFY — frozen curator-given content.
-/

/-- Returns `true` iff `s` starts with `"0b"` and the rest are `'0'`/`'1'` characters. -/
def spec_helper_isBinaryStr (s : String) : Bool :=
  s.startsWith "0b" && (s.toList.drop 2).all (fun c => c == '0' || c == '1')

/-- Parse a `"0b…"` string to its non-negative integer value.
    Assumes the string is well-formed (use after `spec_helper_isBinaryStr`). -/
def spec_helper_parseBinary (s : String) : Int :=
  (s.toList.drop 2).foldl (fun acc c => acc * 2 + if c == '1' then 1 else 0) (0 : Int)

/-- `binary_and` always returns a well-formed binary literal `"0b…"` for non-negative inputs. -/
def spec_and_valid_format (impl : RepoImpl) : Prop :=
  ∀ (a b : Int), 0 ≤ a → 0 ≤ b →
    spec_helper_isBinaryStr (impl.bitManipulation.binary_and a b) = true

/-- The integer decoded from `binary_and a b` equals the bitwise AND of `a` and `b`. -/
def spec_and_value (impl : RepoImpl) : Prop :=
  ∀ (a b : Int), 0 ≤ a → 0 ≤ b →
    spec_helper_parseBinary (impl.bitManipulation.binary_and a b) =
      ((a.toNat &&& b.toNat : Nat) : Int)

/-- `binary_and` is commutative: `binary_and a b = binary_and b a` as strings. -/
def spec_and_commutes (impl : RepoImpl) : Prop :=
  ∀ (a b : Int), 0 ≤ a → 0 ≤ b →
    impl.bitManipulation.binary_and a b = impl.bitManipulation.binary_and b a

/-- `binary_and` returns byte-exactly the upstream Python reference output (`BitHelpers.binaryAndString`).
    Stronger than `spec_and_value`, which only constrains the decoded integer. -/
def spec_and_matches_reference (impl : RepoImpl) : Prop :=
  ∀ (a b : Int), 0 ≤ a → 0 ≤ b →
    impl.bitManipulation.binary_and a b = BitHelpers.binaryAndString a b

/-- De Morgan at the integer level: within the shared bit-width
    `w = max (Nat.log2 a + 1) (Nat.log2 b + 1)`,
    `AND(a,b)` equals `NOT (OR (NOT a) (NOT b))`. -/
def spec_and_or_de_morgan (impl : RepoImpl) : Prop :=
  ∀ (a b : Int), 0 ≤ a → 0 ≤ b →
    let w := Nat.max (Nat.log2 a.toNat + 1) (Nat.log2 b.toNat + 1)
    let mask : Nat := 2 ^ w - 1
    spec_helper_parseBinary (impl.bitManipulation.binary_and a b) =
      ((Nat.xor (Nat.lor (Nat.xor a.toNat mask) (Nat.xor b.toNat mask)) mask : Nat) : Int)

/-- Absorption: `AND a (OR a b) = a` and `OR a (AND a b) = a` at the decoded-integer level. -/
def spec_and_or_absorption (impl : RepoImpl) : Prop :=
  ∀ (a b : Int), 0 ≤ a → 0 ≤ b →
    let or_ab := spec_helper_parseBinary (impl.bitManipulation.binary_or a b)
    let and_ab := spec_helper_parseBinary (impl.bitManipulation.binary_and a b)
    spec_helper_parseBinary (impl.bitManipulation.binary_and a or_ab) = a ∧
    spec_helper_parseBinary (impl.bitManipulation.binary_or a and_ab) = a

/-- Identity / annihilator with `0`: `AND a 0 = 0`; `OR a 0 = a` (decoded values). -/
def spec_and_or_zero_identity (impl : RepoImpl) : Prop :=
  ∀ (a : Int), 0 ≤ a →
    spec_helper_parseBinary (impl.bitManipulation.binary_and a 0) = 0 ∧
    spec_helper_parseBinary (impl.bitManipulation.binary_or a 0) = a

/-- Concrete-value regression points for `binary_and`. -/
def spec_ground_and (impl : RepoImpl) : Prop :=
  spec_helper_parseBinary (impl.bitManipulation.binary_and 25 32) = 0 ∧
  spec_helper_parseBinary (impl.bitManipulation.binary_and 37 50) = 32 ∧
  spec_helper_parseBinary (impl.bitManipulation.binary_and 256 256) = 256
