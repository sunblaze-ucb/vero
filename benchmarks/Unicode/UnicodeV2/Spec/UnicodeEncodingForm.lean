import UnicodeV2.Harness

/-!
# Unicode.Spec.UnicodeEncodingForm

Specifications for the Unicode encoding form interface. Each `spec_*`
is a property over an arbitrary `impl : RepoImpl`.

These specs capture the core invariants of an abstract Unicode encoding form:
round-trip consistency between split/prepend, partition of minimal subsequences,
and closure of well-formedness under concatenation and flattening.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- A code unit sequence is well-formed iff it can be partitioned into
    minimal well-formed code unit subsequences. Defined via `impl` so specs
    can reason about any candidate implementation. -/
def isWellFormedCodeUnitSequence (impl : RepoImpl) (s : CodeUnitSeq) : Bool :=
  (impl.unicodeV2.uefPartitionCodeUnitSequenceChecked s).isSome

/-- Splitting the prefix of a prepended minimal well-formed subsequence returns
    exactly that subsequence. -/
def spec_splitPrefix_inverts_prepend (impl : RepoImpl) : Prop :=
  ∀ (m : MinimalWellFormedCodeUnitSeq) (s : CodeUnitSeq),
    impl.unicodeV2.uefIsMinimalWellFormedCodeUnitSubsequence m = true →
    impl.unicodeV2.uefSplitPrefixMinimalWellFormedCodeUnitSubsequence (m ++ s) = some m

/-- Partitioning a minimal well-formed code unit subsequence yields the singleton
    list containing exactly that subsequence. -/
def spec_partition_minimal_is_singleton (impl : RepoImpl) : Prop :=
  ∀ (m : MinimalWellFormedCodeUnitSeq),
    impl.unicodeV2.uefIsMinimalWellFormedCodeUnitSubsequence m = true →
    impl.unicodeV2.uefPartitionCodeUnitSequenceChecked m = some [m]

/-- Every minimal well-formed code unit subsequence is itself a well-formed
    code unit sequence. -/
def spec_minimal_implies_wellformed (impl : RepoImpl) : Prop :=
  ∀ (m : MinimalWellFormedCodeUnitSeq),
    impl.unicodeV2.uefIsMinimalWellFormedCodeUnitSubsequence m = true →
    isWellFormedCodeUnitSequence impl m = true

/-- Prepending a minimal well-formed subsequence to a well-formed sequence
    yields a well-formed sequence. -/
def spec_prepend_minimal_preserves_wellformed (impl : RepoImpl) : Prop :=
  ∀ (m : MinimalWellFormedCodeUnitSeq) (s : CodeUnitSeq),
    impl.unicodeV2.uefIsMinimalWellFormedCodeUnitSubsequence m = true →
    isWellFormedCodeUnitSequence impl s = true →
    isWellFormedCodeUnitSequence impl (m ++ s) = true

/-- Joining a list of minimal well-formed code unit subsequences produces a
    well-formed code unit sequence. -/
def spec_flatten_minimal_is_wellformed (impl : RepoImpl) : Prop :=
  ∀ (ms : List MinimalWellFormedCodeUnitSeq),
    (∀ m ∈ ms, impl.unicodeV2.uefIsMinimalWellFormedCodeUnitSubsequence m = true) →
    isWellFormedCodeUnitSequence impl ms.flatten = true

/-- Concatenating two well-formed code unit sequences yields a well-formed
    code unit sequence. -/
def spec_concat_wellformed_is_wellformed (impl : RepoImpl) : Prop :=
  ∀ (s t : CodeUnitSeq),
    isWellFormedCodeUnitSequence impl s = true →
    isWellFormedCodeUnitSequence impl t = true →
    isWellFormedCodeUnitSequence impl (s ++ t) = true

/-- Helper coverage spec: encoding and then decoding one scalar value returns
    the same scalar value. This is source-adjacent behavior for the abstract
    encoding form, kept as a manifest `spec_helper` rather than a direct source
    lemma obligation. -/
def spec_encode_decode_scalar_roundtrip (impl : RepoImpl) : Prop :=
  ∀ (v : ScalarValue),
    impl.unicodeV2.uefDecodeMinimalWellFormedCodeUnitSubsequence
      (impl.unicodeV2.uefEncodeScalarValue v) = v

/-- Helper coverage spec: encoding a scalar sequence yields a well-formed code
    unit sequence according to the checked partition operation. -/
def spec_encode_sequence_is_wellformed (impl : RepoImpl) : Prop :=
  ∀ (vs : List ScalarValue),
    isWellFormedCodeUnitSequence impl (impl.unicodeV2.uefEncodeScalarSequence vs) = true

/-- Helper coverage spec: checked decoding agrees with unchecked decoding on
    inputs accepted as well-formed. -/
def spec_decode_checked_agrees_with_decode (impl : RepoImpl) : Prop :=
  ∀ (s : CodeUnitSeq) (vs : List ScalarValue),
    impl.unicodeV2.uefDecodeCodeUnitSequenceChecked s = some vs →
    impl.unicodeV2.uefDecodeCodeUnitSequence s = vs

/-- Helper coverage spec: the unchecked partition API agrees with the checked
    partition API whenever the erased Lean input satisfies the source
    well-formedness precondition. -/
def spec_partition_checked_agrees_with_partition (impl : RepoImpl) : Prop :=
  ∀ (s : CodeUnitSeq) (parts : List MinimalWellFormedCodeUnitSeq),
    impl.unicodeV2.uefPartitionCodeUnitSequenceChecked s = some parts →
    impl.unicodeV2.uefPartitionCodeUnitSequence s = parts
