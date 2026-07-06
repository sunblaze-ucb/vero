import UnicodeV2.Impl.Unicode
import UnicodeV2.Impl.UnicodeEncodingForm
import UnicodeV2.Impl.AbstractUnicodeStrings
import UnicodeV2.Impl.Utf8EncodingForm
import UnicodeV2.Impl.Utf16EncodingForm
import UnicodeV2.Impl.Utf8EncodingScheme
import UnicodeV2.Impl.UnicodeStringsWithoutUnicodeChar
import UnicodeV2.Impl.UnicodeStringsWithUnicodeChar

/-!
# Unicode.Bundle

Per-package implementation bundle for the `Unicode` root package.
Collects all 30 API signatures into one structure.

In `Harness.lean`, `RepoImpl` is a structure with a single `unicode` field of
type `UnicodeV2Bundle` (single-package benchmark).

DO NOT MODIFY — benchmark infrastructure.
-/

structure UnicodeV2Bundle where
  -- UnicodeEncodingForm APIs (abstract encoding form)
  uefIsMinimalWellFormedCodeUnitSubsequence      : Unicode.UefIsMinimalWellFormedCodeUnitSubsequenceSig
  uefSplitPrefixMinimalWellFormedCodeUnitSubsequence : Unicode.UefSplitPrefixMinimalWellFormedCodeUnitSubsequenceSig
  uefEncodeScalarValue                           : Unicode.UefEncodeScalarValueSig
  uefDecodeMinimalWellFormedCodeUnitSubsequence  : Unicode.UefDecodeMinimalWellFormedCodeUnitSubsequenceSig
  uefPartitionCodeUnitSequenceChecked            : Unicode.UefPartitionCodeUnitSequenceCheckedSig
  uefEncodeScalarSequence                        : Unicode.UefEncodeScalarSequenceSig
  uefDecodeCodeUnitSequence                      : Unicode.UefDecodeCodeUnitSequenceSig
  uefDecodeCodeUnitSequenceChecked               : Unicode.UefDecodeCodeUnitSequenceCheckedSig
  -- AbstractUnicodeStrings APIs
  absToUTF8Checked                               : Unicode.AbsToUTF8CheckedSig
  absASCIIToUTF8                                 : Unicode.AbsASCIIToUTF8Sig
  absFromUTF8Checked                             : Unicode.AbsFromUTF8CheckedSig
  absToUTF16Checked                              : Unicode.AbsToUTF16CheckedSig
  absASCIIToUTF16                                : Unicode.AbsASCIIToUTF16Sig
  absFromUTF16Checked                            : Unicode.AbsFromUTF16CheckedSig
  -- Utf8EncodingForm APIs
  utf8IsMinimalWellFormedCodeUnitSubsequence     : Unicode.Utf8IsMinimalWellFormedCodeUnitSubsequenceSig
  utf8SplitPrefixMinimalWellFormedCodeUnitSubsequence : Unicode.Utf8SplitPrefixMinimalWellFormedCodeUnitSubsequenceSig
  utf8EncodeScalarValue                          : Unicode.Utf8EncodeScalarValueSig
  utf8DecodeMinimalWellFormedCodeUnitSubsequence : Unicode.Utf8DecodeMinimalWellFormedCodeUnitSubsequenceSig
  -- Utf16EncodingForm APIs
  utf16IsMinimalWellFormedCodeUnitSubsequence     : Unicode.Utf16IsMinimalWellFormedCodeUnitSubsequenceSig
  utf16SplitPrefixMinimalWellFormedCodeUnitSubsequence : Unicode.Utf16SplitPrefixMinimalWellFormedCodeUnitSubsequenceSig
  utf16EncodeScalarValue                          : Unicode.Utf16EncodeScalarValueSig
  utf16DecodeMinimalWellFormedCodeUnitSubsequence : Unicode.Utf16DecodeMinimalWellFormedCodeUnitSubsequenceSig
  -- Utf8EncodingScheme APIs
  serialize                                      : Unicode.SerializeSig
  deserialize                                    : Unicode.DeserializeSig
  -- Review-gated UnicodeEncodingForm API with erased subset-type input.
  uefPartitionCodeUnitSequence                   : Unicode.UefPartitionCodeUnitSequenceSig
  -- UnicodeStringsWithoutUnicodeChar APIs
  noCharToUTF8Checked                            : Unicode.NoCharToUTF8CheckedSig
  noCharFromUTF8Checked                          : Unicode.NoCharFromUTF8CheckedSig
  noCharToUTF16Checked                           : Unicode.NoCharToUTF16CheckedSig
  noCharFromUTF16Checked                         : Unicode.NoCharFromUTF16CheckedSig
  -- UnicodeStringsWithUnicodeChar APIs
  uniCharToUTF8Checked                           : Unicode.UniCharToUTF8CheckedSig
  uniCharFromUTF8Checked                         : Unicode.UniCharFromUTF8CheckedSig
  uniCharToUTF16Checked                          : Unicode.UniCharToUTF16CheckedSig
  uniCharFromUTF16Checked                        : Unicode.UniCharFromUTF16CheckedSig
