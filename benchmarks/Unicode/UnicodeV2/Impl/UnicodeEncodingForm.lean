import UnicodeV2.Impl.Unicode

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Unicode.Impl.UnicodeEncodingForm

Abstract interface for a Unicode encoding form (Section 3.9 D79–D92).

An encoding form assigns each Unicode scalar value to a unique code unit
sequence. This module defines the abstract API contract — `uefIsMinimalWellFormedCodeUnitSubsequence`,
`uefSplitPrefixMinimalWellFormedCodeUnitSubsequence`, `uefEncodeScalarValue`,
and `uefDecodeMinimalWellFormedCodeUnitSubsequence` are the four primitive
abstract operations; the remaining functions are concrete and defined in terms
of those primitives.

The reference implementation provided here uses a trivial UTF-32-like scheme
where each scalar value maps to a single code unit equal to its code point value.

Types and signatures are fixed vocabulary (DO NOT MODIFY).
-/

-- ── Types (DO NOT MODIFY) ──────────────────────────────────────────────

/-- The minimal bit combination for a unit of encoded text. (Section 3.9 D77.) -/
abbrev UefCodeUnit := Nat

/-- A sequence of code units. -/
abbrev CodeUnitSeq := List UefCodeUnit

/-- A code unit sequence that can be partitioned into minimal well-formed
    code unit subsequences. -/
abbrev WellFormedCodeUnitSeq := List UefCodeUnit

/-- A well-formed code unit subsequence that encodes exactly one scalar value
    and has no proper well-formed prefix. (Section 3.9 D85a.) -/
abbrev MinimalWellFormedCodeUnitSeq := List UefCodeUnit

namespace Unicode

-- ── API signatures (DO NOT MODIFY) ────────────────────────────────────

abbrev UefIsMinimalWellFormedCodeUnitSubsequenceSig :=
  CodeUnitSeq → Bool

abbrev UefSplitPrefixMinimalWellFormedCodeUnitSubsequenceSig :=
  CodeUnitSeq → Option MinimalWellFormedCodeUnitSeq

abbrev UefEncodeScalarValueSig :=
  ScalarValue → MinimalWellFormedCodeUnitSeq

abbrev UefDecodeMinimalWellFormedCodeUnitSubsequenceSig :=
  MinimalWellFormedCodeUnitSeq → ScalarValue

abbrev UefPartitionCodeUnitSequenceCheckedSig :=
  CodeUnitSeq → Option (List MinimalWellFormedCodeUnitSeq)

abbrev UefPartitionCodeUnitSequenceSig :=
  WellFormedCodeUnitSeq → List MinimalWellFormedCodeUnitSeq

abbrev UefEncodeScalarSequenceSig :=
  List ScalarValue → WellFormedCodeUnitSeq

abbrev UefDecodeCodeUnitSequenceSig :=
  WellFormedCodeUnitSeq → List ScalarValue

abbrev UefDecodeCodeUnitSequenceCheckedSig :=
  CodeUnitSeq → Option (List ScalarValue)

end Unicode

-- !benchmark @start global_aux
-- Helper: test whether a Nat is a valid scalar value code point.
private def isValidScalarCodePoint (n : Nat) : Bool :=
  n ≤ 0x10FFFF &&
  !(HIGH_SURROGATE_MIN ≤ n && n ≤ HIGH_SURROGATE_MAX) &&
  !(LOW_SURROGATE_MIN  ≤ n && n ≤ LOW_SURROGATE_MAX)

-- Fallback scalar value: U+0000 (NULL character).
private def nullScalarValue : ScalarValue :=
  ⟨⟨0, by omega⟩,
   ⟨Or.inl (by simp [HIGH_SURROGATE_MIN]),
    Or.inl (by simp [LOW_SURROGATE_MIN])⟩⟩

-- Helper: build a ScalarValue from a Nat, falling back to U+0000.
private def natToScalarValue (n : Nat) : ScalarValue :=
  if h₁ : n ≤ 0x10FFFF then
    if h₂ : (n < HIGH_SURROGATE_MIN ∨ n > HIGH_SURROGATE_MAX) ∧
             (n < LOW_SURROGATE_MIN  ∨ n > LOW_SURROGATE_MAX) then
      ⟨⟨n, h₁⟩, h₂⟩
    else
      nullScalarValue
  else
    nullScalarValue
-- !benchmark @end global_aux

-- ── Implementation stubs ───────────────────────────────────────────────

-- !benchmark @start code_aux def=uefIsMinimalWellFormedCodeUnitSubsequence
-- !benchmark @end code_aux def=uefIsMinimalWellFormedCodeUnitSubsequence

def Unicode.uefIsMinimalWellFormedCodeUnitSubsequence : Unicode.UefIsMinimalWellFormedCodeUnitSubsequenceSig :=
-- !benchmark @start code def=uefIsMinimalWellFormedCodeUnitSubsequence
  fun s =>
    match s with
    | [n] => isValidScalarCodePoint n
    | _   => false
-- !benchmark @end code def=uefIsMinimalWellFormedCodeUnitSubsequence

-- !benchmark @start code_aux def=uefSplitPrefixMinimalWellFormedCodeUnitSubsequence
-- !benchmark @end code_aux def=uefSplitPrefixMinimalWellFormedCodeUnitSubsequence

def Unicode.uefSplitPrefixMinimalWellFormedCodeUnitSubsequence : Unicode.UefSplitPrefixMinimalWellFormedCodeUnitSubsequenceSig :=
-- !benchmark @start code def=uefSplitPrefixMinimalWellFormedCodeUnitSubsequence
  fun s =>
    match s with
    | []      => none
    | n :: _ =>
      if isValidScalarCodePoint n then some [n]
      else none
-- !benchmark @end code def=uefSplitPrefixMinimalWellFormedCodeUnitSubsequence

-- !benchmark @start code_aux def=uefEncodeScalarValue
-- !benchmark @end code_aux def=uefEncodeScalarValue

def Unicode.uefEncodeScalarValue : Unicode.UefEncodeScalarValueSig :=
-- !benchmark @start code def=uefEncodeScalarValue
  fun v => [v.val.val]
-- !benchmark @end code def=uefEncodeScalarValue

-- !benchmark @start code_aux def=uefDecodeMinimalWellFormedCodeUnitSubsequence
-- !benchmark @end code_aux def=uefDecodeMinimalWellFormedCodeUnitSubsequence

def Unicode.uefDecodeMinimalWellFormedCodeUnitSubsequence : Unicode.UefDecodeMinimalWellFormedCodeUnitSubsequenceSig :=
-- !benchmark @start code def=uefDecodeMinimalWellFormedCodeUnitSubsequence
  fun m =>
    match m with
    | [n] => natToScalarValue n
    | _   => natToScalarValue 0
-- !benchmark @end code def=uefDecodeMinimalWellFormedCodeUnitSubsequence

-- !benchmark @start code_aux def=uefPartitionCodeUnitSequenceChecked
-- !benchmark @end code_aux def=uefPartitionCodeUnitSequenceChecked

def Unicode.uefPartitionCodeUnitSequenceChecked : Unicode.UefPartitionCodeUnitSequenceCheckedSig :=
-- !benchmark @start code def=uefPartitionCodeUnitSequenceChecked
  fun s =>
    s.mapM (fun n =>
      if isValidScalarCodePoint n then some [n]
      else none)
-- !benchmark @end code def=uefPartitionCodeUnitSequenceChecked

-- !benchmark @start code_aux def=uefPartitionCodeUnitSequence
-- !benchmark @end code_aux def=uefPartitionCodeUnitSequence

def Unicode.uefPartitionCodeUnitSequence : Unicode.UefPartitionCodeUnitSequenceSig :=
-- !benchmark @start code def=uefPartitionCodeUnitSequence
  -- Dafny's source type guarantees well-formed input. Lean represents that
  -- subset type as `List Nat`, so malformed aliases fall back to the empty
  -- partition outside the source precondition.
  fun s => (Unicode.uefPartitionCodeUnitSequenceChecked s).getD []
-- !benchmark @end code def=uefPartitionCodeUnitSequence

-- !benchmark @start code_aux def=uefEncodeScalarSequence
-- !benchmark @end code_aux def=uefEncodeScalarSequence

def Unicode.uefEncodeScalarSequence : Unicode.UefEncodeScalarSequenceSig :=
-- !benchmark @start code def=uefEncodeScalarSequence
  fun vs => vs.map (fun v => v.val.val)
-- !benchmark @end code def=uefEncodeScalarSequence

-- !benchmark @start code_aux def=uefDecodeCodeUnitSequence
-- !benchmark @end code_aux def=uefDecodeCodeUnitSequence

def Unicode.uefDecodeCodeUnitSequence : Unicode.UefDecodeCodeUnitSequenceSig :=
-- !benchmark @start code def=uefDecodeCodeUnitSequence
  fun s => s.map natToScalarValue
-- !benchmark @end code def=uefDecodeCodeUnitSequence

-- !benchmark @start code_aux def=uefDecodeCodeUnitSequenceChecked
-- !benchmark @end code_aux def=uefDecodeCodeUnitSequenceChecked

def Unicode.uefDecodeCodeUnitSequenceChecked : Unicode.UefDecodeCodeUnitSequenceCheckedSig :=
-- !benchmark @start code def=uefDecodeCodeUnitSequenceChecked
  fun s =>
    s.mapM (fun n =>
      if isValidScalarCodePoint n then some (natToScalarValue n)
      else none)
-- !benchmark @end code def=uefDecodeCodeUnitSequenceChecked
