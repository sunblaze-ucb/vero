/-!
# Json.Impl.Errors

Foundation error vocabulary translated from `JSON.Errors`.

DO NOT MODIFY types or signatures - these are the fixed vocabulary.
-/

namespace JSON

-- Types (no markers - fixed vocabulary)

inductive DeserializationError where
  | unterminatedSequence
  | unsupportedEscape (str : String)
  | escapeAtEOS
  | emptyNumber
  | expectingEOF
  | intOverflow
  | reachedEOF
  | expectingByte (expected : UInt8) (b : Option UInt8)
  | expectingAnyByte (expected_sq : List UInt8) (b : Option UInt8)
  | invalidUnicode
  deriving Repr, DecidableEq, BEq

inductive SerializationError where
  | outOfMemory
  | intTooLarge (i : Int)
  | stringTooLong (s : String)
  | invalidUnicode
  deriving Repr, DecidableEq, BEq

abbrev SerializationResult (T : Type) := Except SerializationError T

abbrev DeserializationResult (T : Type) := Except DeserializationError T

end JSON
