import JsonV2.Impl.Errors
import JsonV2.Impl.Utils.Views
import JsonV2.Impl.Utils.Cursors
import JsonV2.Impl.Utils.Parsers
import JsonV2.Impl.Grammar

/-!
# Json.Impl.ZeroCopy.Deserializer

Zero-copy deserializer vocabulary translated from
`JSON.ZeroCopy.Deserializer`.

DO NOT MODIFY types or signatures - these are the fixed vocabulary.
-/

namespace JSON

-- Types (no markers - fixed vocabulary)

abbrev JSONError := DeserializationError

abbrev ParseResult (T : Type) := SplitResult T JSONError

abbrev Parser (T : Type) := FreshCursor → ParseResult T

abbrev SubParser (T : Type) := FreshCursor → ParseResult T

abbrev jopt := View_

abbrev ValueParser := SubParser GrammarValue

abbrev TElement := GrammarValue

abbrev jopen := View_

abbrev jclose := View_

abbrev TBracketed := Bracketed jopen TElement jcomma jclose

abbrev TSuffixedElement := Suffixed TElement jcomma

-- Spec helpers (no markers - fixed vocabulary)

def specView (v : View_) : List UInt8 := view__Bytes v

def jsonBlankByte (b : UInt8) : Bool := b == 0x20 || b == 0x09 || b == 0x0A || b == 0x0D

def cursor__prefix (cs : Cursor_) : View_ := { s := cs.s, beg := cs.beg, end_ := cs.point }

def cursor__suffix (cs : Cursor_) : FreshCursor := { cs with beg := cs.point }

def cursor__split (cs : Cursor_) : Split View_ := { t := cursor__prefix cs, cs := cursor__suffix cs }

def cursor__skipByte (cs : Cursor_) : Cursor_ :=
  if cs.point.toNat < cs.end_.toNat then
    { cs with point := UInt32.ofNat (cs.point.toNat + 1) }
  else
    cs

def cursor__skipWhile (p : UInt8 → Bool) (cs : Cursor_) : Cursor_ :=
  let rec go (fuel point : Nat) : Nat :=
    match fuel with
    | 0 => point
    | fuel + 1 =>
      if point < cs.end_.toNat then
        match cs.s[point]? with
        | some b => if p b then go fuel (point + 1) else point
        | none => point
      else
        point
  { cs with point := UInt32.ofNat (go (cs.end_.toNat - cs.point.toNat) cs.point.toNat) }

def zeroCopyWS (cs : FreshCursor) : Split jblanks := cursor__split (cursor__skipWhile jsonBlankByte cs)

def tryStructural (cs : FreshCursor) : Split (Structural jopt) :=
  let before := zeroCopyWS cs
  let val := cursor__split (cursor__skipByte before.cs)
  let after := zeroCopyWS val.cs
  { t := { before := before.t, t := val.t, after := after.t }, cs := after.cs }

def openByte : UInt8 := 91

def closeByte : UInt8 := 93

def separatorByte : UInt8 := 44

end JSON
