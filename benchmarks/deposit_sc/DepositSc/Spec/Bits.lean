import DepositSc.Harness

/-!
# DepositSc.Spec.Bits

Specifications for the bit-list primitives. Each `spec_*` is a
property over an arbitrary `impl : RepoImpl`.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- `power2` agrees with `2^n`. Even though `power2` is fully
    expressible in standard library terms, the Dafny source keeps it
    as a dedicated helper and uses it in every size bound. -/
def spec_power2 (impl : RepoImpl) : Prop :=
  ∀ (n : Nat), impl.depositSc.power2 n = 2 ^ n

/-- `bitListToNat ∘ natToBitList = id` for natural numbers below the
    bit-length cap. Dafny: `bitToNatToBitsIsIdentity`. -/
def spec_bit_list_round_trip (impl : RepoImpl) : Prop :=
  ∀ (n len : Nat),
    n < impl.depositSc.power2 len →
    impl.depositSc.bitListToNat (impl.depositSc.natToBitList n len) = n

/-- `natToBitList n len` has length `len`. Dafny `natToBitList`
    `ensures` clause. -/
def spec_nat_to_bit_list_length (impl : RepoImpl) : Prop :=
  ∀ (n len : Nat),
    (impl.depositSc.natToBitList n len).length = len

/-- `natToBitList 0 len` is all zeros. -/
def spec_nat_to_bit_list_zero (impl : RepoImpl) : Prop :=
  ∀ (len : Nat),
    (impl.depositSc.natToBitList 0 len).all (fun b => b.val = 0) = true

/-- `nextPath` is the binary successor on bit lists (valid whenever
    the path isn't all-ones). Dafny: `nextPathIsSucc`. -/
def spec_next_path_succ (impl : RepoImpl) : Prop :=
  ∀ (p : Path),
    impl.depositSc.bitListToNat p + 1 < impl.depositSc.power2 p.length →
    impl.depositSc.bitListToNat (impl.depositSc.nextPath p)
      = impl.depositSc.bitListToNat p + 1

/-- `nextPath` preserves length. Dafny: part of `nextPath`'s
    `ensures`. -/
def spec_next_path_length (impl : RepoImpl) : Prop :=
  ∀ (p : Path),
    impl.depositSc.bitListToNat p + 1 < impl.depositSc.power2 p.length →
    (impl.depositSc.nextPath p).length = p.length

/-- `nextPath (natToBitList n len)` equals `natToBitList (n+1) len`
    whenever `n + 1 < 2^len`. Dafny: `pathToSucc`. -/
def spec_next_path_nat_to_bit_list (impl : RepoImpl) : Prop :=
  ∀ (n len : Nat),
    n + 1 < impl.depositSc.power2 len →
    impl.depositSc.nextPath (impl.depositSc.natToBitList n len)
      = impl.depositSc.natToBitList (n + 1) len

/-- `zipCond` has the length of its selector list. Dafny:
    `zipCond` postcondition. -/
def spec_zip_cond_length (impl : RepoImpl) : Prop :=
  ∀ (c : List Bit) (a b : List Int),
    a.length = c.length → b.length = c.length →
    (impl.depositSc.zipCond c a b).length = c.length

/-- `zipCond` on an all-zero selector picks elements from `a`. Dafny:
    `zipCond_zero_left`. -/
def spec_zip_cond_zero_left (impl : RepoImpl) : Prop :=
  ∀ (n : Nat) (a b : List Int),
    a.length = n → b.length = n →
    impl.depositSc.zipCond (List.replicate n ⟨0, by decide⟩) a b = a

/-- `zipCond` on an all-one selector picks elements from `b`. Dafny:
    `zipCond_one_right`. -/
def spec_zip_cond_one_right (impl : RepoImpl) : Prop :=
  ∀ (n : Nat) (a b : List Int),
    a.length = n → b.length = n →
    impl.depositSc.zipCond (List.replicate n ⟨1, by decide⟩) a b = b

/-- `zeroes f d h` has length `h + 1`. Dafny: `zeroes` postcondition. -/
def spec_zeroes_length (impl : RepoImpl) : Prop :=
  ∀ (f : MergeFn) (d : Int) (h : Nat),
    (impl.depositSc.zeroes f d h).length = h + 1

/-- The `i`-th entry of `zeroes f d h` is `defaultValue f d i`. -/
def spec_zeroes_get (impl : RepoImpl) : Prop :=
  ∀ (f : MergeFn) (d : Int) (h i : Nat),
    i ≤ h →
    (impl.depositSc.zeroes f d h)[i]? = some (impl.depositSc.defaultValue f d i)

/-- Base case of `defaultValue`: level 0 is the default `d`. -/
def spec_default_value_zero (impl : RepoImpl) : Prop :=
  ∀ (f : MergeFn) (d : Int),
    impl.depositSc.defaultValue f d 0 = d

/-- Recursive case of `defaultValue`: level `k+1` applies `f` to two
    copies of the level-`k` value. -/
def spec_default_value_succ (impl : RepoImpl) : Prop :=
  ∀ (f : MergeFn) (d : Int) (k : Nat),
    impl.depositSc.defaultValue f d (k + 1)
      = f (impl.depositSc.defaultValue f d k) (impl.depositSc.defaultValue f d k)

/-- Appending a bit multiplies the value by 2 and adds the bit.
    Dafny: `simplifyPrefixBitListToNat` in `SeqOfBits.dfy`. -/
def spec_bit_list_nat_of_snoc (impl : RepoImpl) : Prop :=
  ∀ (p : Path) (b : Bit),
    impl.depositSc.bitListToNat (p ++ [b])
      = 2 * impl.depositSc.bitListToNat p + b.val

/-- The all-ones bit list of length `n` encodes `2^n - 1`. Dafny:
    `valueOfSeqOfOnes` in `SeqOfBits.dfy`. -/
def spec_value_of_seq_of_ones (impl : RepoImpl) : Prop :=
  ∀ (n : Nat),
    impl.depositSc.bitListToNat (List.replicate n ⟨1, by decide⟩)
      = impl.depositSc.power2 n - 1

/-- Dropping the leaf-level entry of `zeroes` yields the zeroes list
    one level up (i.e. under the new default `f d d`). Dafny:
    `shiftZeroesPrefix` in `RightSiblings.dfy` (adapted to Lean's
    ascending `zeroes` convention — see `Impl/Bits.lean`). -/
def spec_shift_zeroes_prefix (impl : RepoImpl) : Prop :=
  ∀ (f : MergeFn) (d : Int) (h : Nat),
    1 ≤ h →
    (impl.depositSc.zeroes f d h).drop 1
      = impl.depositSc.zeroes f (f d d) (h - 1)

/-- Doubling identity for `power2`: `2^(n+1) = 2^n + 2^n`. Dafny:
    `power2Lemmas` in `Helpers.dfy`. -/
def spec_power2_add (impl : RepoImpl) : Prop :=
  ∀ (n : Nat),
    impl.depositSc.power2 (n + 1)
      = impl.depositSc.power2 n + impl.depositSc.power2 n

/-- Halving identity for `power2`: `2^n / 2 = 2^(n-1)` when `n ≥ 1`.
    Dafny: `power2Div2` in `Helpers.dfy`. -/
def spec_power2_div2 (impl : RepoImpl) : Prop :=
  ∀ (n : Nat),
    1 ≤ n →
    impl.depositSc.power2 n / 2 = impl.depositSc.power2 (n - 1)

/-- `bitListToNat` is injective on equal-length bit lists: two bit
    lists of the same length encoding the same natural number are
    equal. Dafny: `sameNatSameBitList` in `SeqOfBits.dfy`. -/
def spec_same_nat_same_bit_list (impl : RepoImpl) : Prop :=
  ∀ (p p' : Path),
    p.length = p'.length →
    impl.depositSc.bitListToNat p = impl.depositSc.bitListToNat p' →
    p = p'

/-- Converse of `spec_next_path_succ`: any bit list that encodes the
    successor of `p` (and has the same length) equals `nextPath p`.
    Dafny: `succIsNextPath` in `SeqOfBits.dfy`. -/
def spec_succ_is_next_path (impl : RepoImpl) : Prop :=
  ∀ (p p' : Path),
    p.length = p'.length →
    impl.depositSc.bitListToNat p + 1 < impl.depositSc.power2 p.length →
    impl.depositSc.bitListToNat p' = impl.depositSc.bitListToNat p + 1 →
    p' = impl.depositSc.nextPath p

/-- Biconditional form of `spec_next_path_succ` combining
    `spec_next_path_succ` and `spec_succ_is_next_path`. Dafny:
    `nextPathIffSucc` in `SeqOfBits.dfy`. -/
def spec_next_path_iff_succ (impl : RepoImpl) : Prop :=
  ∀ (p p' : Path),
    p.length = p'.length →
    impl.depositSc.bitListToNat p + 1 < impl.depositSc.power2 p.length →
    (p' = impl.depositSc.nextPath p ↔
     impl.depositSc.bitListToNat p' = impl.depositSc.bitListToNat p + 1)

/-- `bitListToNat p = 0` if and only if every bit of `p` is zero.
    Dafny: `valueIsZeroImpliesAllZeroes` in `SeqOfBits.dfy`
    (stated here as the stronger biconditional). -/
def spec_bit_list_zero_iff_all_zero (impl : RepoImpl) : Prop :=
  ∀ (p : Path),
    impl.depositSc.bitListToNat p = 0 ↔ ∀ i, i < p.length → (p[i]?).map Fin.val = some 0

/-- Any bit list encoding a value strictly less than the maximum
    `2^|p| - 1` must contain at least one zero bit — i.e. `nextPath`'s
    precondition ("some bit is 0") holds. Dafny: `pathToNoLasthasZero`
    in `SeqOfBits.dfy`. -/
def spec_path_not_max_has_zero (impl : RepoImpl) : Prop :=
  ∀ (p : Path),
    1 ≤ p.length →
    impl.depositSc.bitListToNat p < impl.depositSc.power2 p.length - 1 →
    ∃ i, i < p.length ∧ (p[i]?).map Fin.val = some 0
