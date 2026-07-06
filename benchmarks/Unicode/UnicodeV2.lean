import UnicodeV2.Impl.Unicode
import UnicodeV2.Impl.UnicodeEncodingForm
import UnicodeV2.Impl.AbstractUnicodeStrings
import UnicodeV2.Impl.Utf8EncodingForm
import UnicodeV2.Impl.Utf16EncodingForm
import UnicodeV2.Impl.Utf8EncodingScheme
import UnicodeV2.Impl.UnicodeStringsWithoutUnicodeChar
import UnicodeV2.Impl.UnicodeStringsWithUnicodeChar
import UnicodeV2.Bundle
import UnicodeV2.Harness
import UnicodeV2.Spec.Unicode
import UnicodeV2.Spec.UnicodeEncodingForm
import UnicodeV2.Spec.AbstractUnicodeStrings
import UnicodeV2.Spec.Utf8EncodingForm
import UnicodeV2.Spec.Utf16EncodingForm
import UnicodeV2.Spec.Utf8EncodingScheme
import UnicodeV2.Spec.UnicodeStringsWithoutUnicodeChar
import UnicodeV2.Spec.UnicodeStringsWithUnicodeChar
import UnicodeV2.Test

/-!
# UnicodeV2

Root import hub for the Unicode v2 benchmark translated from the Dafny
`dafny-lang/libraries` Unicode library.

This version restores the broad Unicode surface selected by curation:
abstract encoding-form operations, UTF-8 and UTF-16 encoding forms, UTF-8
encoding scheme serialization, and the two Dafny string models.
-/
