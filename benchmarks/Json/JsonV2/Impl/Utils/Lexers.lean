-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Json.Impl.Utils.Lexers

Lexer vocabulary and reference implementations translated from
`JSON.Utils.Lexers`.

DO NOT MODIFY types or signatures - these are the fixed vocabulary.
Implement only the function bodies.
-/

namespace JSON

-- Types (no markers - fixed vocabulary)

inductive LexerResult (T R : Type) where
  | accept : LexerResult T R
  | reject (err : R) : LexerResult T R
  | partial_ (st : T) : LexerResult T R
  deriving Repr, DecidableEq, BEq

abbrev Lexer (T R : Type) := T → Option UInt8 → LexerResult T R

abbrev StringBodyLexerState := Bool

inductive StringLexerState where
  | start : StringLexerState
  | body (escaped : Bool) : StringLexerState
  | end_ : StringLexerState
  deriving Repr, DecidableEq, BEq

-- Spec helpers (no markers - fixed vocabulary)

def stringBodyLexerStart : StringBodyLexerState := false

def stringLexerStart : StringLexerState := .start

-- API signatures (no markers - fixed vocabulary)

abbrev StringBodySig := (R : Type) → Lexer StringBodyLexerState R

abbrev LexStringSig := Lexer StringLexerState String

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- !benchmark @start code_aux def=stringBody
-- !benchmark @end code_aux def=stringBody

def stringBody : StringBodySig :=
-- !benchmark @start code def=stringBody
  fun _R escaped byte =>
    if byte == some (92 : UInt8) then
      .partial_ (!escaped)
    else if byte == some (34 : UInt8) && !escaped then
      .accept
    else
      .partial_ false
-- !benchmark @end code def=stringBody

-- !benchmark @start code_aux def=lexString
-- !benchmark @end code_aux def=lexString

def lexString : LexStringSig :=
-- !benchmark @start code def=lexString
  fun st byte =>
    match st with
    | .start =>
      if byte == some (34 : UInt8) then
        .partial_ (.body false)
      else
        .reject "String must start with double quote"
    | .body escaped =>
      if byte == some (92 : UInt8) then
        .partial_ (.body (!escaped))
      else if byte == some (34 : UInt8) && !escaped then
        .partial_ .end_
      else
        .partial_ (.body false)
    | .end_ =>
      .accept
-- !benchmark @end code def=lexString

end JSON
