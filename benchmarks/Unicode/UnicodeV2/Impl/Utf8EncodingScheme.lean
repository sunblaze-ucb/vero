import UnicodeV2.Impl.Utf8EncodingForm

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Unicode.Impl.Utf8EncodingScheme

The Unicode encoding scheme that serializes a UTF-8 code unit sequence in exactly the
same order as the code unit sequence itself (Unicode 14.0, Section 3.10 D95).

Because UTF-8 deals in ordered byte sequences, the encoding scheme is trivial: the byte
ordering is completely defined by the UTF-8 code unit sequence itself. The only work is
the (trivial) conversion between `UInt8`/`byte` and `bv8` values — both are 8-bit
unsigned integers so the cast is a no-op.

Types and signatures are fixed vocabulary (DO NOT MODIFY). Function bodies are the
curator's reference implementations; the pipeline replaces them with `sorry` inside
the `code` markers before presenting the benchmark to the LLM.
-/

-- ── Types (DO NOT MODIFY) ─────────────────────────────────────────────────────

-- `Utf8CodeUnit` is imported from Unicode.Impl.Utf8EncodingForm.

/-- A serialized UTF-8 byte: an 8-bit unsigned integer (corresponds to Dafny `uint8`). -/
abbrev Utf8Byte := UInt8

namespace Unicode

-- ── API signatures (DO NOT MODIFY) ────────────────────────────────────────────

/-- Signature for serializing a UTF-8 code unit sequence to a byte sequence. -/
abbrev SerializeSig := List Utf8CodeUnit → List Utf8Byte

/-- Signature for deserializing a byte sequence to a UTF-8 code unit sequence. -/
abbrev DeserializeSig := List Utf8Byte → List Utf8CodeUnit

end Unicode

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- ── Implementation stubs (LLM task) ───────────────────────────────────────────

-- !benchmark @start code_aux def=serialize
-- !benchmark @end code_aux def=serialize

def Unicode.serialize : Unicode.SerializeSig :=
-- !benchmark @start code def=serialize
  -- UTF-8 code units (bv8) and bytes (uint8) are both 8-bit unsigned integers.
  -- The cast is a no-op: each element maps to itself.
  fun s => s
-- !benchmark @end code def=serialize

-- !benchmark @start code_aux def=deserialize
-- !benchmark @end code_aux def=deserialize

def Unicode.deserialize : Unicode.DeserializeSig :=
-- !benchmark @start code def=deserialize
  -- Bytes (uint8) and UTF-8 code units (bv8) are both 8-bit unsigned integers.
  -- The cast is a no-op: each element maps to itself.
  fun b => b
-- !benchmark @end code def=deserialize
