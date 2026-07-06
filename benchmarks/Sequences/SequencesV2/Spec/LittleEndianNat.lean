import SequencesV2.Harness

/-!
# SequencesV2.Spec.LittleEndianNat

Frozen specifications for little-endian natural-number sequence operations
translated from `Collections/Sequences/LittleEndianNat.dfy`. Each spec is a
property over an arbitrary `impl : RepoImpl`.

DO NOT MODIFY - this file is frozen curator-given content.
-/

open SequencesV2

/-- The two definitions of little-endian numeric interpretation agree. -/
def spec_LittleEndianNat_LemmaToNatLeftEqToNatRight (impl : RepoImpl) : Prop :=
  ∀ (model : LittleEndianNat_Model), ∀ (xs : List LittleEndianNat_uint),
    LittleEndianNat_validSeq model xs →
      impl.sequences.LittleEndianNat_ToNatRight model xs =
        impl.sequences.LittleEndianNat_ToNatLeft model xs

/-- Proof-helper task exposing ToNatRight and ToNatLeft equality for all valid sequences. -/
def proof_helper_LittleEndianNat_LemmaToNatLeftEqToNatRightAuto (impl : RepoImpl) : Prop :=
  ∀ (model : LittleEndianNat_Model), ∀ (xs : List LittleEndianNat_uint),
    LittleEndianNat_validSeq model xs →
      impl.sequences.LittleEndianNat_ToNatRight model xs =
        impl.sequences.LittleEndianNat_ToNatLeft model xs

/-- A one-digit sequence denotes its first digit. -/
def spec_LittleEndianNat_LemmaSeqLen1 (impl : RepoImpl) : Prop :=
  ∀ (model : LittleEndianNat_Model),
    ∀ (xs : List LittleEndianNat_uint) (_hLen : xs.length = 1) (hNonempty : xs.length > 0),
      LittleEndianNat_validSeq model xs →
        impl.sequences.LittleEndianNat_ToNatRight model xs =
          impl.sequences.Seq_First xs hNonempty

/-- A two-digit sequence denotes low digit plus high digit times the base. -/
def spec_LittleEndianNat_LemmaSeqLen2 (impl : RepoImpl) : Prop :=
  ∀ (model : LittleEndianNat_Model),
    ∀ (xs : List LittleEndianNat_uint) (_hLen : xs.length = 2) (hNonempty : xs.length > 0),
      LittleEndianNat_validSeq model xs →
        impl.sequences.LittleEndianNat_ToNatRight model xs =
          impl.sequences.Seq_First xs hNonempty +
            match xs[1]? with
            | some x => x * (LittleEndianNat_BASE model)
            | none => 0

/-- Appending a zero most-significant digit does not change the numeric interpretation. -/
def spec_LittleEndianNat_LemmaSeqAppendZero (impl : RepoImpl) : Prop :=
  ∀ (model : LittleEndianNat_Model), ∀ (xs : List LittleEndianNat_uint),
    LittleEndianNat_validSeq model xs →
      impl.sequences.LittleEndianNat_ToNatRight model (xs ++ [0]) =
        impl.sequences.LittleEndianNat_ToNatRight model xs

/-- A valid digit sequence denotes a number below base^length. -/
def spec_LittleEndianNat_LemmaSeqNatBound (impl : RepoImpl) : Prop :=
  ∀ (model : LittleEndianNat_Model), ∀ (xs : List LittleEndianNat_uint),
    LittleEndianNat_validSeq model xs →
      impl.sequences.LittleEndianNat_ToNatRight model xs <
        PowNat (LittleEndianNat_BASE model) xs.length

/-- The numeric value can be split into prefix and suffix contributions. -/
def spec_LittleEndianNat_LemmaSeqPrefix (impl : RepoImpl) : Prop :=
  ∀ (model : LittleEndianNat_Model), ∀ (xs : List LittleEndianNat_uint) (i : Nat),
    LittleEndianNat_validSeq model xs →
      i ≤ xs.length →
        impl.sequences.LittleEndianNat_ToNatRight model (Seq_Slice xs 0 i) +
            impl.sequences.LittleEndianNat_ToNatRight model (Seq_Slice xs i xs.length) *
              PowNat (LittleEndianNat_BASE model) i =
          impl.sequences.LittleEndianNat_ToNatRight model xs

/-- If equal-length sequences differ by a larger most-significant digit, the numeric interpretation is larger. -/
def proof_helper_LittleEndianNat_LemmaSeqMswInequality (impl : RepoImpl) : Prop :=
  ∀ (model : LittleEndianNat_Model),
    ∀ (xs ys : List LittleEndianNat_uint) (hx : xs.length > 0) (hy : ys.length > 0),
      LittleEndianNat_validSeq model xs →
        LittleEndianNat_validSeq model ys →
          xs.length = ys.length →
            impl.sequences.Seq_Last xs hx < impl.sequences.Seq_Last ys hy →
              impl.sequences.LittleEndianNat_ToNatRight model xs <
                impl.sequences.LittleEndianNat_ToNatRight model ys

/-- Unequal numeric prefixes imply unequal full numeric interpretations. -/
def proof_helper_LittleEndianNat_LemmaSeqPrefixNeq (impl : RepoImpl) : Prop :=
  ∀ (model : LittleEndianNat_Model), ∀ (xs ys : List LittleEndianNat_uint) (i : Nat),
    LittleEndianNat_validSeq model xs →
      LittleEndianNat_validSeq model ys →
        i ≤ xs.length →
          xs.length = ys.length →
            impl.sequences.LittleEndianNat_ToNatRight model (Seq_Slice xs 0 i) ≠
              impl.sequences.LittleEndianNat_ToNatRight model (Seq_Slice ys 0 i) →
                impl.sequences.LittleEndianNat_ToNatRight model xs ≠
                  impl.sequences.LittleEndianNat_ToNatRight model ys

/-- Distinct equal-length digit sequences have distinct numeric interpretations. -/
def spec_LittleEndianNat_LemmaSeqNeq (impl : RepoImpl) : Prop :=
  ∀ (model : LittleEndianNat_Model), ∀ (xs ys : List LittleEndianNat_uint),
    LittleEndianNat_validSeq model xs →
      LittleEndianNat_validSeq model ys →
        xs.length = ys.length →
          xs ≠ ys →
            impl.sequences.LittleEndianNat_ToNatRight model xs ≠
              impl.sequences.LittleEndianNat_ToNatRight model ys

/-- Equal-length digit sequences with equal numeric interpretations are equal. -/
def spec_LittleEndianNat_LemmaSeqEq (impl : RepoImpl) : Prop :=
  ∀ (model : LittleEndianNat_Model), ∀ (xs ys : List LittleEndianNat_uint),
    LittleEndianNat_validSeq model xs →
      LittleEndianNat_validSeq model ys →
        xs.length = ys.length →
          impl.sequences.LittleEndianNat_ToNatRight model xs =
            impl.sequences.LittleEndianNat_ToNatRight model ys →
              xs = ys

/-- The least-significant digit is congruent to the numeric value modulo the base. -/
def spec_LittleEndianNat_LemmaSeqLswModEquivalence (impl : RepoImpl) : Prop :=
  ∀ (model : LittleEndianNat_Model),
    ∀ (xs : List LittleEndianNat_uint) (_h : xs.length ≥ 1) (hNonempty : xs.length > 0),
      LittleEndianNat_validSeq model xs →
        (impl.sequences.LittleEndianNat_ToNatRight model xs) % (LittleEndianNat_BASE model) =
          impl.sequences.Seq_First xs hNonempty

/-- FromNat produces no more than len digits when n is below base^len. -/
def proof_helper_LittleEndianNat_LemmaFromNatLen (impl : RepoImpl) : Prop :=
  ∀ (model : LittleEndianNat_Model), ∀ (n len : Nat),
    PowNat (LittleEndianNat_BASE model) len > n →
      (impl.sequences.LittleEndianNat_FromNat model n).length ≤ len

/-- Converting a nat to a sequence and back gives the original nat. -/
def spec_LittleEndianNat_LemmaNatSeqNat (impl : RepoImpl) : Prop :=
  ∀ (model : LittleEndianNat_Model), ∀ (n : Nat),
    impl.sequences.LittleEndianNat_ToNatRight model
        (impl.sequences.LittleEndianNat_FromNat model n) =
      n

/-- FromNat returns the canonical little-endian digit sequence for n. -/
def spec_LittleEndianNat_FromNat___ensures_spec (impl : RepoImpl) : Prop :=
  ∀ (model : LittleEndianNat_Model), ∀ (n : Nat),
    let xs := impl.sequences.LittleEndianNat_FromNat model n
    LittleEndianNat_validSeq model xs ∧
      impl.sequences.LittleEndianNat_ToNatRight model xs = n ∧
      (n = 0 → xs = []) ∧
      (n > 0 →
        xs = [n % LittleEndianNat_BASE model] ++
          impl.sequences.LittleEndianNat_FromNat model (n / LittleEndianNat_BASE model))

/-- SeqExtend returns length n and preserves the numeric interpretation. -/
def spec_LittleEndianNat_SeqExtend___ensures_spec (impl : RepoImpl) : Prop :=
  ∀ (model : LittleEndianNat_Model),
    ∀ (xs : List LittleEndianNat_uint) (n : Nat) (h : xs.length ≤ n),
      let ys := impl.sequences.LittleEndianNat_SeqExtend model xs n h
      ys.length = n ∧
        impl.sequences.LittleEndianNat_ToNatRight model ys =
          impl.sequences.LittleEndianNat_ToNatRight model xs ∧
        (LittleEndianNat_validSeq model xs → LittleEndianNat_validSeq model ys)

/-- SeqExtendMultiple pads to a multiple of n and preserves numeric interpretation. -/
def spec_LittleEndianNat_SeqExtendMultiple___ensures_spec (impl : RepoImpl) : Prop :=
  ∀ (model : LittleEndianNat_Model),
    ∀ (xs : List LittleEndianNat_uint) (n : Nat) (h : n > 0),
      let ys := impl.sequences.LittleEndianNat_SeqExtendMultiple model xs n h
      ys.length = xs.length + n - (xs.length % n) ∧
        ys.length % n = 0 ∧
        (∀ i, i < xs.length → ys[i]? = xs[i]?) ∧
        (∀ i, xs.length ≤ i → i < ys.length → ys[i]? = some 0) ∧
        impl.sequences.LittleEndianNat_ToNatRight model ys =
          impl.sequences.LittleEndianNat_ToNatRight model xs ∧
        (LittleEndianNat_validSeq model xs → LittleEndianNat_validSeq model ys)

/-- FromNatWithLen produces exactly len valid digits representing n. -/
def spec_LittleEndianNat_FromNatWithLen___ensures_spec (impl : RepoImpl) : Prop :=
  ∀ (model : LittleEndianNat_Model),
    ∀ (n len : Nat) (h : PowNat (LittleEndianNat_BASE model) len > n),
      let xs := impl.sequences.LittleEndianNat_FromNatWithLen model n len h
      xs.length = len ∧
        impl.sequences.LittleEndianNat_ToNatRight model xs = n ∧
        LittleEndianNat_validSeq model xs

/-- A sequence with numeric value zero consists only of zero digits. -/
def spec_LittleEndianNat_LemmaSeqZero (impl : RepoImpl) : Prop :=
  ∀ (model : LittleEndianNat_Model), ∀ (xs : List LittleEndianNat_uint),
    impl.sequences.LittleEndianNat_ToNatRight model xs = 0 →
      ∀ i, i < xs.length → xs[i]? = some 0

/-- SeqZero returns len zero digits with numeric value zero. -/
def spec_LittleEndianNat_SeqZero___ensures_spec (impl : RepoImpl) : Prop :=
  ∀ (model : LittleEndianNat_Model), ∀ (len : Nat),
    let xs := impl.sequences.LittleEndianNat_SeqZero model len
    xs.length = len ∧
      (∀ i, i < xs.length → xs[i]? = some 0) ∧
      impl.sequences.LittleEndianNat_ToNatRight model xs = 0 ∧
      LittleEndianNat_validSeq model xs

/-- Converting a valid sequence to a nat and back at the same length recovers the sequence. -/
def spec_LittleEndianNat_LemmaSeqNatSeq (impl : RepoImpl) : Prop :=
  ∀ (model : LittleEndianNat_Model),
    ∀ (xs : List LittleEndianNat_uint)
      (h : PowNat (LittleEndianNat_BASE model) xs.length >
        impl.sequences.LittleEndianNat_ToNatRight model xs),
      LittleEndianNat_validSeq model xs →
        impl.sequences.LittleEndianNat_FromNatWithLen model
            (impl.sequences.LittleEndianNat_ToNatRight model xs) xs.length h =
          xs

/-- SeqAdd returns a same-length valid result and a carry bit. -/
def spec_LittleEndianNat_SeqAdd___ensures_spec (impl : RepoImpl) : Prop :=
  ∀ (model : LittleEndianNat_Model),
    ∀ (xs ys : List LittleEndianNat_uint) (h : xs.length = ys.length),
      let r := impl.sequences.LittleEndianNat_SeqAdd model xs ys h
      r.1.length = xs.length ∧
        r.2 ≤ 1 ∧
        (LittleEndianNat_validSeq model xs →
          LittleEndianNat_validSeq model ys →
            LittleEndianNat_validSeq model r.1)

/-- SeqAdd matches addition of numeric interpretations plus final carry. -/
def spec_LittleEndianNat_LemmaSeqAdd (impl : RepoImpl) : Prop :=
  ∀ (model : LittleEndianNat_Model),
    ∀ (xs ys zs : List LittleEndianNat_uint) (cout : Nat) (h : xs.length = ys.length),
      LittleEndianNat_validSeq model xs →
        LittleEndianNat_validSeq model ys →
          impl.sequences.LittleEndianNat_SeqAdd model xs ys h = (zs, cout) →
            impl.sequences.LittleEndianNat_ToNatRight model xs +
                impl.sequences.LittleEndianNat_ToNatRight model ys =
              impl.sequences.LittleEndianNat_ToNatRight model zs +
                cout * PowNat (LittleEndianNat_BASE model) xs.length

/-- SeqSub returns a same-length valid result and a borrow bit. -/
def spec_LittleEndianNat_SeqSub___ensures_spec (impl : RepoImpl) : Prop :=
  ∀ (model : LittleEndianNat_Model),
    ∀ (xs ys : List LittleEndianNat_uint) (h : xs.length = ys.length),
      let r := impl.sequences.LittleEndianNat_SeqSub model xs ys h
      r.1.length = xs.length ∧
        r.2 ≤ 1 ∧
        (LittleEndianNat_validSeq model xs →
          LittleEndianNat_validSeq model ys →
            LittleEndianNat_validSeq model r.1)

/-- SeqSub matches subtraction of numeric interpretations plus final borrow. -/
def spec_LittleEndianNat_LemmaSeqSub (impl : RepoImpl) : Prop :=
  ∀ (model : LittleEndianNat_Model),
    ∀ (xs ys zs : List LittleEndianNat_uint) (cout : Nat) (h : xs.length = ys.length),
      LittleEndianNat_validSeq model xs →
        LittleEndianNat_validSeq model ys →
          impl.sequences.LittleEndianNat_SeqSub model xs ys h = (zs, cout) →
            impl.sequences.LittleEndianNat_ToNatRight model xs +
                cout * PowNat (LittleEndianNat_BASE model) xs.length =
              impl.sequences.LittleEndianNat_ToNatRight model zs +
                impl.sequences.LittleEndianNat_ToNatRight model ys
