import VestV2.Impl.RegularTag
import VestV2.Harness

/-!
# VestV2.Spec.RegularTag

Specifications for the Tag combinator module. Each `spec_*` is a
property over an arbitrary `impl : RepoImpl`.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- Tag.spec_parse returns Some iff the inner parse succeeds and the
    parsed value satisfies the predicate; always returns unit on
    success. -/
def spec_tag_parse_correct (_impl : RepoImpl) : Prop :=
  ∀ (Inner T Pred : Type) [SpecCombinator Inner T] [SpecPred Pred T]
    (c : Tag Inner Pred) (s : List UInt8),
  (Tag.spec_parse c s ≠ none) ↔
  (∃ n v, SpecCombinator.spec_parse c.inner s = some (n, v) ∧ SpecPred.spec_pred c.tagger v = true)

/-- For Tag, serializing a well-formed (predicate-satisfying) value
    then parsing gives back unit at the same length. -/
def spec_tag_serialize_parse_roundtrip (_impl : RepoImpl) : Prop :=
  ∀ (Inner T Pred : Type) [SpecCombinator Inner T] [SpecPred Pred T]
    (c : Tag Inner Pred) (v : T),
  SpecPred.spec_pred c.tagger v = true →
  SpecCombinator.spec_parse c.inner (SpecCombinator.spec_serialize c.inner v) = some (((SpecCombinator.spec_serialize c.inner v).length : Int), v) →
  Tag.spec_parse c (Tag.spec_serialize c v) = some (((Tag.spec_serialize c v).length : Int), ())

/-- tagParse tag s returns Ok(1, ()) iff the first byte of s equals
    tag, and Err otherwise. -/
def spec_tag_parse_u8_correct (impl : RepoImpl) : Prop :=
  ∀ (tag : UInt8) (s : List UInt8),
  (s.head? = some tag → impl.vest.tagParse tag s = Except.ok (1, ())) ∧
  (s.head? ≠ some tag → ∃ e, impl.vest.tagParse tag s = Except.error e)

/-- tagSerialize has exactly one observable success mode: if one byte
    fits at `pos`, it reports that one byte was written. Otherwise it
    returns InsufficientBuffer. -/
def spec_tag_serialize_u8_correct (impl : RepoImpl) : Prop :=
  ∀ (tag : UInt8) (buf : List UInt8) (pos : Nat),
    (pos + 1 ≤ buf.length → impl.vest.tagSerialize tag () buf pos = Except.ok 1) ∧
    (buf.length < pos + 1 →
      impl.vest.tagSerialize tag () buf pos = Except.error SerializeError.InsufficientBuffer)
