import SequencesV2.Harness

/-!
# SequencesV2.Spec.LittleEndianNatConversions

Frozen specifications for little-endian natural-number conversions translated
from `Collections/Sequences/LittleEndianNatConversions.dfy`. Each spec is a
property over an arbitrary `impl : RepoImpl`.

DO NOT MODIFY - this file is frozen curator-given content.
-/

open SequencesV2

/-- ToSmall expands each large digit into E small digits. -/
def spec_LittleEndianNatConversions_ToSmall___ensures_spec (impl : RepoImpl) : Prop :=
  ∀ (model : LittleEndianNatConversions_Model), ∀ (xs : List Large_uint),
    let ys := impl.sequences.LittleEndianNatConversions_ToSmall model xs
    ys.length = xs.length * (LittleEndianNatConversions_E model) ∧
      (Large_validSeq model xs → Small_validSeq model ys)

/-- ToLarge packs every E small digits into one large digit. -/
def spec_LittleEndianNatConversions_ToLarge___ensures_spec (impl : RepoImpl) : Prop :=
  ∀ (model : LittleEndianNatConversions_Model),
    ∀ (xs : List Small_uint) (h : xs.length % (LittleEndianNatConversions_E model) = 0),
      let ys := impl.sequences.LittleEndianNatConversions_ToLarge model xs h
      ys.length = xs.length / (LittleEndianNatConversions_E model) ∧
        (Small_validSeq model xs → Large_validSeq model ys)

/-- Converting from large to small base preserves numeric interpretation. -/
def spec_LittleEndianNatConversions_LemmaToSmall (impl : RepoImpl) : Prop :=
  ∀ (model : LittleEndianNatConversions_Model), ∀ (xs : List Large_uint),
    Large_validSeq model xs →
      Small_ToNatRight model (impl.sequences.LittleEndianNatConversions_ToSmall model xs) =
        Large_ToNatRight model xs

/-- Converting from small to large base preserves numeric interpretation. -/
def spec_LittleEndianNatConversions_LemmaToLarge (impl : RepoImpl) : Prop :=
  ∀ (model : LittleEndianNatConversions_Model),
    ∀ (xs : List Small_uint) (h : xs.length % (LittleEndianNatConversions_E model) = 0),
      Small_validSeq model xs →
        Large_ToNatRight model (impl.sequences.LittleEndianNatConversions_ToLarge model xs h) =
          Small_ToNatRight model xs

/-- ToSmall is injective for equal-length valid large-base sequences. -/
def spec_LittleEndianNatConversions_LemmaToSmallIsInjective (impl : RepoImpl) : Prop :=
  ∀ (model : LittleEndianNatConversions_Model), ∀ (xs ys : List Large_uint),
    Large_validSeq model xs →
      Large_validSeq model ys →
        impl.sequences.LittleEndianNatConversions_ToSmall model xs =
          impl.sequences.LittleEndianNatConversions_ToSmall model ys →
            xs.length = ys.length →
              xs = ys

/-- ToLarge is injective for equal-length valid small-base sequences whose lengths are multiples of E. -/
def spec_LittleEndianNatConversions_LemmaToLargeIsInjective (impl : RepoImpl) : Prop :=
  ∀ (model : LittleEndianNatConversions_Model),
    ∀ (xs ys : List Small_uint)
      (hx : xs.length % (LittleEndianNatConversions_E model) = 0)
      (hy : ys.length % (LittleEndianNatConversions_E model) = 0),
      Small_validSeq model xs →
        Small_validSeq model ys →
          impl.sequences.LittleEndianNatConversions_ToLarge model xs hx =
            impl.sequences.LittleEndianNatConversions_ToLarge model ys hy →
              xs.length = ys.length →
                xs = ys

/-- Converting a valid small-base sequence to large and back recovers it. -/
def spec_LittleEndianNatConversions_LemmaSmallLargeSmall (impl : RepoImpl) : Prop :=
  ∀ (model : LittleEndianNatConversions_Model),
    ∀ (xs : List Small_uint)
      (h : xs.length % (LittleEndianNatConversions_E model) = 0)
      (_hback :
        (impl.sequences.LittleEndianNatConversions_ToLarge model xs h).length *
            (LittleEndianNatConversions_E model) %
          (LittleEndianNatConversions_E model) =
        0),
      Small_validSeq model xs →
        impl.sequences.LittleEndianNatConversions_ToSmall model
            (impl.sequences.LittleEndianNatConversions_ToLarge model xs h) =
          xs

/-- Converting a valid large-base sequence to small and back recovers it. -/
def spec_LittleEndianNatConversions_LemmaLargeSmallLarge (impl : RepoImpl) : Prop :=
  ∀ (model : LittleEndianNatConversions_Model),
    ∀ (xs : List Large_uint)
      (h :
        (impl.sequences.LittleEndianNatConversions_ToSmall model xs).length %
            (LittleEndianNatConversions_E model) =
          0),
      Large_validSeq model xs →
        (impl.sequences.LittleEndianNatConversions_ToSmall model xs).length %
            (LittleEndianNatConversions_E model) =
          0 ∧
          impl.sequences.LittleEndianNatConversions_ToLarge model
              (impl.sequences.LittleEndianNatConversions_ToSmall model xs) h =
            xs

/-- Reference proof-helper equality property for large-base digit sequences. -/
def proof_helper_Large_LemmaSeqEq (_impl : RepoImpl) : Prop :=
  ∀ (model : LittleEndianNatConversions_Model), ∀ (xs ys : List Large_uint),
    Large_validSeq model xs →
      Large_validSeq model ys →
        xs.length = ys.length →
          Large_ToNatRight model xs = Large_ToNatRight model ys →
            xs = ys

/-- Reference proof-helper equality property for small-base digit sequences. -/
def proof_helper_Small_LemmaSeqEq (_impl : RepoImpl) : Prop :=
  ∀ (model : LittleEndianNatConversions_Model), ∀ (xs ys : List Small_uint),
    Small_validSeq model xs →
      Small_validSeq model ys →
        xs.length = ys.length →
          Small_ToNatRight model xs = Small_ToNatRight model ys →
            xs = ys

/-- Reference proof-helper bound for small-base numeric interpretation. -/
def proof_helper_Small_LemmaSeqNatBound (_impl : RepoImpl) : Prop :=
  ∀ (model : LittleEndianNatConversions_Model), ∀ (xs : List Small_uint),
    Small_validSeq model xs →
      Small_ToNatRight model xs < PowNat (SmallSeq_BASE model) xs.length

/-- Reference proof-helper round trip for small-base sequences. -/
def proof_helper_Small_LemmaSeqNatSeq (_impl : RepoImpl) : Prop :=
  ∀ (model : LittleEndianNatConversions_Model),
    ∀ (xs : List Small_uint)
      (h : PowNat (SmallSeq_BASE model) xs.length > Small_ToNatRight model xs),
      Small_validSeq model xs →
        Small_FromNatWithLen model (Small_ToNatRight model xs) xs.length h = xs

/-- Reference proof-helper prefix decomposition for small-base sequences. -/
def proof_helper_Small_LemmaSeqPrefix (_impl : RepoImpl) : Prop :=
  ∀ (model : LittleEndianNatConversions_Model), ∀ (xs : List Small_uint) (i : Nat),
    Small_validSeq model xs →
      i ≤ xs.length →
        Small_ToNatRight model (Seq_Slice xs 0 i) +
            Small_ToNatRight model (Seq_Slice xs i xs.length) *
              PowNat (SmallSeq_BASE model) i =
          Small_ToNatRight model xs
