import VestV2.Impl.RegularModifier

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# VestV2.Impl.RegularTag

Tag combinator for the VestV2 parser/serializer framework.
`TagPred` is a predicate that matches a value against a stored tag.
`Tag` pairs an inner combinator with a tag predicate, parsing to unit
on match and failing otherwise. Concrete `tagParse` and `tagSerialize`
implement the `Tag<U8, u8>` specialization.

Types and signatures are fixed vocabulary (DO NOT MODIFY). Function
bodies are the curator's reference implementations.

`SpecPred` is imported from `RegularModifier`.
-/

-- ── Types (DO NOT MODIFY) ─────────────────────────────────

/-- Tag predicate that matches the input with a given value. -/
structure TagPred (T : Type) where
  tag : T

/-- Generic tag combinator: pairs an inner combinator with a tagger
    (predicate), parsing succeeds with `()` iff the inner parse
    succeeds and the value satisfies the predicate. -/
structure Tag (Inner Tagger : Type) where
  inner : Inner
  tagger : Tagger

-- ── Spec helpers (no markers — fixed vocabulary) ──────────

/-- Spec parse for Tag: parse with inner, check predicate, return unit
    on success. -/
def Tag.spec_parse {Inner T Pred : Type} [SpecCombinator Inner T] [SpecPred Pred T]
    (c : Tag Inner Pred) (s : List UInt8) : Option (Int × Unit) :=
  match SpecCombinator.spec_parse c.inner s with
  | some (n, v) =>
    if SpecPred.spec_pred c.tagger v then some (n, ())
    else none
  | none => none

/-- Spec serialize for Tag: serialize the given value with the inner
    combinator. -/
def Tag.spec_serialize {Inner T Pred : Type} [SpecCombinator Inner T]
    (c : Tag Inner Pred) (v : T) : List UInt8 :=
  SpecCombinator.spec_serialize c.inner v

namespace VestV2

-- ── API signatures (DO NOT MODIFY) ───────────────────────

/-- Parse for Tag<U8, u8>: read one byte and succeed with (1, ()) iff
    it equals the expected tag value; otherwise return error. -/
abbrev TagParseSig := UInt8 → List UInt8 → Except ParseError (Nat × Unit)

/-- Serialize for Tag<U8, u8>: write the expected tag byte to buf at
    pos; returns 1 on success. -/
abbrev TagSerializeSig := UInt8 → Unit → List UInt8 → Nat → Except SerializeError Nat

end VestV2

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- ── Implementation stubs (LLM task) ────────────────────────

-- !benchmark @start code_aux def=tagParse
-- !benchmark @end code_aux def=tagParse

def VestV2.tagParse : VestV2.TagParseSig :=
-- !benchmark @start code def=tagParse
  fun tag s =>
    match s with
    | [] => Except.error ParseError.UnexpectedEndOfInput
    | b :: _ =>
      if b == tag then Except.ok (1, ())
      else Except.error ParseError.RefinedPredicateFailed
-- !benchmark @end code def=tagParse

-- !benchmark @start code_aux def=tagSerialize
-- !benchmark @end code_aux def=tagSerialize

def VestV2.tagSerialize : VestV2.TagSerializeSig :=
-- !benchmark @start code def=tagSerialize
  fun _tag () buf pos =>
    if pos + 1 ≤ buf.length then
      Except.ok 1
    else
      Except.error SerializeError.InsufficientBuffer
-- !benchmark @end code def=tagSerialize
