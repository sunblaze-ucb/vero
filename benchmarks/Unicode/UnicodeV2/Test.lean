import UnicodeV2.Impl.Utf8EncodingScheme
import UnicodeV2.Impl.Utf8EncodingForm
import UnicodeV2.Impl.Utf16EncodingForm
import UnicodeV2.Impl.UnicodeEncodingForm
import UnicodeV2.Impl.AbstractUnicodeStrings
import UnicodeV2.Impl.UnicodeStringsWithUnicodeChar
import UnicodeV2.Spec.UnicodeStringsWithoutUnicodeChar

/-!
# UnicodeV2.Test

Executable conformance guards for the curator reference implementations.
-/

private def svA : ScalarValue := ⟨⟨0x41, by decide⟩, by decide⟩
private def svEuro : ScalarValue := ⟨⟨0x20AC, by decide⟩, by decide⟩
private def svSmile : ScalarValue := ⟨⟨0x1F600, by decide⟩, by decide⟩
private def euroString : String := String.singleton ⟨(0x20AC : UInt32), by decide⟩
private def smileString : String := String.singleton ⟨(0x1F600 : UInt32), by decide⟩

-- UnicodeEncodingForm: abstract UTF-32-like model
#guard Unicode.uefIsMinimalWellFormedCodeUnitSubsequence [0x41] == true
#guard Unicode.uefIsMinimalWellFormedCodeUnitSubsequence [0xD800] == false
#guard Unicode.uefSplitPrefixMinimalWellFormedCodeUnitSubsequence [0x41, 0x20AC] == some [0x41]
#guard Unicode.uefEncodeScalarValue svEuro == [0x20AC]
#guard (Unicode.uefDecodeMinimalWellFormedCodeUnitSubsequence [0x20AC]).val.val == 0x20AC
#guard Unicode.uefPartitionCodeUnitSequenceChecked [0x41, 0x20AC] == some [[0x41], [0x20AC]]
#guard Unicode.uefPartitionCodeUnitSequenceChecked [0x41, 0xD800] == none
#guard Unicode.uefPartitionCodeUnitSequence [0x41, 0x20AC] == [[0x41], [0x20AC]]
#guard Unicode.uefEncodeScalarSequence [svA, svEuro] == [0x41, 0x20AC]
#guard (Unicode.uefDecodeCodeUnitSequence [0x41, 0x20AC]).map (fun v => v.val.val) == [0x41, 0x20AC]
#guard (Unicode.uefDecodeCodeUnitSequenceChecked [0x41, 0x20AC]).map (fun vs => vs.map (fun v => v.val.val)) == some [0x41, 0x20AC]
#guard Unicode.uefDecodeCodeUnitSequenceChecked [0xD800] == none

-- AbstractUnicodeStrings: Lean String bridge
#guard Unicode.absToUTF8Checked "" == some []
#guard Unicode.absToUTF8Checked "A" == some [(0x41 : UInt8)]
#guard Unicode.absToUTF8Checked euroString == some [(0xE2 : UInt8), 0x82, 0xAC]
#guard Unicode.absASCIIToUTF8 "AZ" == [(0x41 : UInt8), 0x5A]
#guard Unicode.absFromUTF8Checked [(0x41 : UInt8)] == some "A"
#guard Unicode.absFromUTF8Checked [(0xE2 : UInt8), 0x82, 0xAC] == some euroString
#guard Unicode.absFromUTF8Checked [(0xFF : UInt8)] == none
#guard Unicode.absToUTF16Checked "A" == some [(0x0041 : UInt16)]
#guard Unicode.absToUTF16Checked smileString == some [(0xD83D : UInt16), 0xDE00]
#guard Unicode.absASCIIToUTF16 "AZ" == [(0x0041 : UInt16), 0x005A]
#guard Unicode.absFromUTF16Checked [(0x0041 : UInt16)] == some "A"
#guard Unicode.absFromUTF16Checked [(0xD83D : UInt16), 0xDE00] == some smileString
#guard Unicode.absFromUTF16Checked [(0xD800 : UInt16)] == none

-- Utf8EncodingForm
#guard Unicode.utf8IsMinimalWellFormedCodeUnitSubsequence [(0x41 : UInt8)] == true
#guard Unicode.utf8IsMinimalWellFormedCodeUnitSubsequence [(0xFF : UInt8)] == false
#guard Unicode.utf8IsMinimalWellFormedCodeUnitSubsequence [(0xC3 : UInt8), 0xA9] == true
#guard Unicode.utf8SplitPrefixMinimalWellFormedCodeUnitSubsequence [(0xE2 : UInt8), 0x82, 0xAC, 0x41] == some [(0xE2 : UInt8), 0x82, 0xAC]
#guard Unicode.utf8EncodeScalarValue svEuro == [(0xE2 : UInt8), 0x82, 0xAC]
#guard (Unicode.utf8DecodeMinimalWellFormedCodeUnitSubsequence [(0xE2 : UInt8), 0x82, 0xAC]).val.val == 0x20AC

-- Utf16EncodingForm
#guard Unicode.utf16IsMinimalWellFormedCodeUnitSubsequence [(0x0041 : UInt16)] == true
#guard Unicode.utf16IsMinimalWellFormedCodeUnitSubsequence [(0xD800 : UInt16)] == false
#guard Unicode.utf16IsMinimalWellFormedCodeUnitSubsequence [(0xD800 : UInt16), 0xDC00] == true
#guard Unicode.utf16SplitPrefixMinimalWellFormedCodeUnitSubsequence [(0xD83D : UInt16), 0xDE00, 0x0041] == some [(0xD83D : UInt16), 0xDE00]
#guard Unicode.utf16EncodeScalarValue svSmile == [(0xD83D : UInt16), 0xDE00]
#guard (Unicode.utf16DecodeMinimalWellFormedCodeUnitSubsequence [(0xD83D : UInt16), 0xDE00]).val.val == 0x1F600

-- Utf8EncodingScheme
#guard Unicode.serialize [] == []
#guard Unicode.deserialize [] == []
#guard Unicode.serialize [(0x00 : UInt8), 0x41, 0xFF] == [(0x00 : UInt8), 0x41, 0xFF]
#guard Unicode.deserialize (Unicode.serialize [(0x01 : UInt8), 0x02, 0x80]) == [(0x01 : UInt8), 0x02, 0x80]

-- UnicodeStringsWithoutUnicodeChar
#guard Unicode.isWellFormedString ([] : List UInt16) == true
#guard Unicode.isWellFormedString [(0xD800 : UInt16)] == false
#guard Unicode.noCharToUTF8Checked [(0x0041 : UInt16)] == some [(0x41 : UInt8)]
#guard Unicode.noCharToUTF8Checked [(0xD83D : UInt16), 0xDE00] == some [(0xF0 : UInt8), 0x9F, 0x98, 0x80]
#guard Unicode.noCharToUTF8Checked [(0xD800 : UInt16)] == none
#guard Unicode.noCharFromUTF8Checked [(0x41 : UInt8)] == some [(0x0041 : UInt16)]
#guard Unicode.noCharFromUTF8Checked [(0xF0 : UInt8), 0x9F, 0x98, 0x80] == some [(0xD83D : UInt16), 0xDE00]
#guard Unicode.noCharFromUTF8Checked [(0xFF : UInt8)] == none
#guard Unicode.noCharToUTF16Checked [(0x0041 : UInt16)] == some [(0x0041 : UInt16)]
#guard Unicode.noCharFromUTF16Checked [(0x0041 : UInt16)] == some [(0x0041 : UInt16)]

-- UnicodeStringsWithUnicodeChar
#guard Unicode.uniCharToUTF8Checked "" == some []
#guard Unicode.uniCharToUTF8Checked "A" == some [(0x41 : UInt8)]
#guard Unicode.uniCharToUTF8Checked euroString == some [(0xE2 : UInt8), 0x82, 0xAC]
#guard Unicode.uniCharFromUTF8Checked [(0x41 : UInt8)] == some "A"
#guard Unicode.uniCharFromUTF8Checked [(0xE2 : UInt8), 0x82, 0xAC] == some euroString
#guard Unicode.uniCharFromUTF8Checked [(0xFF : UInt8)] == none
#guard Unicode.uniCharToUTF16Checked "A" == some [(0x0041 : UInt16)]
#guard Unicode.uniCharToUTF16Checked smileString == some [(0xD83D : UInt16), 0xDE00]
#guard Unicode.uniCharFromUTF16Checked [(0x0041 : UInt16)] == some "A"
#guard Unicode.uniCharFromUTF16Checked [(0xD83D : UInt16), 0xDE00] == some smileString
#guard Unicode.uniCharFromUTF16Checked [(0xD800 : UInt16)] == none
