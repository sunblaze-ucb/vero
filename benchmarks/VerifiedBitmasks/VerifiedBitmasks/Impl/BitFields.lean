-- !benchmark @start imports
-- !benchmark @end imports

/-!
# VerifiedBitmasks.Impl.BitFields

BV-level bitwise operations over 64-bit bitvectors (`BitVec 64`).

Provides types, constants, conversion functions, and primitive BV-level
operations used as curator-given vocabulary by higher-level modules.
All definitions here are fully-specified curator helpers — no LLM tasks.

Translated from `src/BitFields/BitFields.i.dfy`.

DO NOT MODIFY types or definitions — these are the fixed vocabulary.
-/

-- ── Types (no markers — fixed vocabulary) ──────────────────────────────────

/-- The machine-word integer type (64-bit unsigned). -/
abbrev I := UInt64

/-- The bitvector type (64-bit). -/
abbrev BV := BitVec 64

-- ── Spec helpers (fully defined, no markers, curator-given) ────────────────

namespace BitFields

/-- The word size in bits (64), typed as the machine integer type `I`.
    Distinct from `MachineTypes.WORD_SIZE : Nat`. -/
def WORD_SIZE : I := 64

end BitFields

/-- The constant with all 64 bits set. -/
def ALL_ONES : UInt64 := 0xffff_ffff_ffff_ffff

/-- Convert a `BitVec 64` to a `UInt64`. -/
def BitsToWord (b : BV) : I := b.toNat.toUInt64

/-- Convert a `UInt64` to a `BitVec 64`. -/
def WordToBits (w : I) : BV := w.toBitVec

/-- Predicate: bit index `i` is in the half-open range `[0, n)`. -/
def InRange (i n : I) : Prop := i.toNat < n.toNat

/-- Convert a `BitVec 64` to a 64-element list of booleans (LSB at index 0). -/
def BitsToSeqBool (b : BV) : List Bool :=
  List.ofFn (fun i : Fin 64 => b.getLsb i)

/-- Internal recursive helper: build a bitvector from `s` starting at `idx`. -/
def SeqBoolToBitsHelper (s : List Bool) (idx : Nat) : BV :=
  let rec go : List Bool → Nat → BV → BV
    | [], _, acc => acc
    | b :: rest, i, acc =>
        let acc' := if i < 64 ∧ b then acc ||| ((1 : BV) <<< i) else acc
        go rest (i + 1) acc'
  go s idx 0

/-- Convert a 64-element boolean list (LSB at index 0) to a `BitVec 64`. -/
def SeqBoolToBits (s : List Bool) : BV := SeqBoolToBitsHelper s 0

/-- Bundle of AND-related bitvector lemmas (idempotent, zero, one, comm, assoc, etc.). -/
def lemma_BitAnd_group : Prop := True

/-- Bundle of OR-related bitvector lemmas (idempotent, identity, ones, comm, assoc, etc.). -/
def lemma_BitOr_group : Prop := True

/-- Bundle of XOR-related bitvector lemmas (self-clear, identity, ones, comm, assoc, etc.). -/
def lemma_BitXor_group : Prop := True

/-- Bundle of NOT/COMP bitvector lemmas (double-negation, equivalence, etc.). -/
def lemma_BitNotComp_group : Prop := True

/-- Bundle of constructor/mask bitvector lemmas (Bit, Ones, Zeros, Mask properties). -/
def lemma_BitConstructor_group : Prop := True

/-- Bundle of equality/individual-bit bitvector lemmas (BitIsSet characterisation, etc.). -/
def lemma_BitEquality_group : Prop := True

/-- Bundle of distribution/DeMorgan bitvector lemmas (And-Or-dist, DeMorgan, etc.). -/
def lemma_BitDistribution_group : Prop := True

-- ── API helpers (fully defined, no markers, curator-given) ─────────────────

/-- Bitvector with only bit `i` set (`1 << i`). -/
def Bit (i : I) : BV := (1 : BV) <<< i.toNat

/-- Bitvector with all 64 bits set. -/
def BitOnes : BV := 0xffff_ffff_ffff_ffff

/-- Bitvector with all bits cleared (zero). -/
def BitZeros : BV := 0

/-- Bitvector mask with the low `i` bits set (`(1 << i) - 1`). -/
def BitMask (i : I) : BV := ((1 : BV) <<< i.toNat) - 1

/-- Bitwise AND of two bitvectors. -/
def BitAnd (x y : BV) : BV := x &&& y

/-- Bitwise OR of two bitvectors. -/
def BitOr (x y : BV) : BV := x ||| y

/-- Bitwise XOR of two bitvectors. -/
def BitXor (x y : BV) : BV := x ^^^ y

/-- Bitwise NOT (complement) of a bitvector. -/
def BitNot (x : BV) : BV := ~~~x

/-- Bitwise complement via XOR with all-ones (identical to `BitNot` for 64-bit). -/
def BitComp (x : BV) : BV := 0xffff_ffff_ffff_ffff ^^^ x

/-- Return `true` if bit `i` of `x` is set. -/
def BitIsSet (x : BV) (i : I) : Bool := BitAnd x (Bit i) != 0

/-- Set bit `i` of `x` (returns `x` with bit `i` forced to 1). -/
def BitSetBit (x : BV) (i : I) : BV := BitOr x (Bit i)

/-- Clear bit `i` of `x` (returns `x` with bit `i` forced to 0). -/
def BitClearBit (x : BV) (i : I) : BV := BitAnd x (BitComp (Bit i))

/-- Toggle bit `i` of `x` (flips bit `i`). -/
def BitToggleBit (x : BV) (i : I) : BV :=
  if BitIsSet x i then BitClearBit x i else BitSetBit x i

/-- Left-shift `x` by `i` bits. -/
def BitLeftShift (x : BV) (i : I) : BV := x <<< i.toNat

/-- Logical right-shift `x` by `i` bits. -/
def BitRightShift (x : BV) (i : I) : BV := x >>> i.toNat

/-- Bitvector addition (wrapping, mod 2^64). -/
def BitAdd (x y : BV) : BV := x + y

/-- Bitvector subtraction (wrapping, mod 2^64). -/
def BitSub (x y : BV) : BV := x - y

/-- Bitvector unsigned modulo (0 when divisor is 0). -/
def BitMod (x y : BV) : BV := x % y

/-- Bitvector unsigned division (0 when divisor is 0). -/
def BitDiv (x y : BV) : BV := x / y

/-- Bitvector multiplication (wrapping, mod 2^64). -/
def BitMul (x y : BV) : BV := x * y
