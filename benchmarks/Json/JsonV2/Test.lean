import JsonV2.Impl.Values
import JsonV2.Impl.Errors
import JsonV2.Impl.Utils.Seq
import JsonV2.Impl.Utils.Str
import JsonV2.Impl.Utils.Views
import JsonV2.Impl.Utils.Views.Writers
import JsonV2.Impl.Utils.Lexers
import JsonV2.Impl.Utils.Cursors
import JsonV2.Impl.Utils.Parsers
import JsonV2.Impl.Utils.Vectors
import JsonV2.Impl.Grammar
import JsonV2.Impl.Spec
import JsonV2.Impl.Serializer
import JsonV2.Impl.Deserializer
import JsonV2.Impl.ConcreteSyntax.Spec
import JsonV2.Impl.ConcreteSyntax.SpecProperties
import JsonV2.Impl.ZeroCopy.Serializer
import JsonV2.Impl.ZeroCopy.Deserializer
import JsonV2.Impl.ZeroCopy.API
import JsonV2.Impl.API
import JsonV2.Impl.Tests
import JsonV2.Impl.Tutorial

/-!
# Json.Test

Executable conformance tests for the curator reference implementations.

DO NOT MODIFY - benchmark infrastructure.
-/

open JSON

-- concat concatenates adjacent strings.
#guard JSON.concat ["a", "b", "c"] == "abc"

-- join inserts separators between strings.
#guard JSON.join "," ["a", "b", "c"] == "a,b,c"

-- concat of an empty list is empty.
#guard JSON.concat [] == ""

-- join of an empty list is empty.
#guard JSON.join "," [] == ""

-- boolean true serializes to ASCII true.
#guard JSON.serializer_bool true == [116, 114, 117, 101]

-- boolean false serializes to ASCII false.
#guard JSON.serializer_bool false == [102, 97, 108, 115, 101]

-- integer zero serializes as ASCII 0.
#guard JSON.intToBytes 0 == "0".toList.map (fun c => UInt8.ofNat c.val.toNat)

-- integer 42 serializes as ASCII 42.
#guard JSON.intToBytes 42 == "42".toList.map (fun c => UInt8.ofNat c.val.toNat)

-- serializer_int succeeds on zero.
#guard
  match JSON.serializer_int 0 with
  | .ok bs => bs == [48]
  | .error _ => false

-- serializer_value handles null.
#guard
  match JSON.serializer_value JSON.JSON.null with
  | .ok bs => bs == [110, 117, 108, 108]
  | .error _ => false

-- empty array serializes to brackets.
#guard
  match JSON.serializer_array [] with
  | .ok bs => bs == [91, 93]
  | .error _ => false

-- empty object serializes to braces.
#guard
  match JSON.serializer_object [] with
  | .ok bs => bs == [123, 125]
  | .error _ => false

-- nonempty array serializes each value with comma separators.
#guard
  match JSON.serializer_array [JSON.JSON.bool true, JSON.JSON.null] with
  | .ok bs => bs == [(91 : UInt8), 116, 114, 117, 101, 44, 110, 117, 108, 108, 93]
  | .error _ => false

-- nonempty object has enough fuel for key-value value serialization.
#guard
  match JSON.serializer_object [("a", JSON.JSON.bool false)] with
  | .ok bs => bs == [(123 : UInt8), 34, 97, 34, 58, 102, 97, 108, 115, 101, 125]
  | .error _ => false

-- view bytes extracts a middle slice.
#guard view__Bytes { s := [(1 : UInt8), 2, 3], beg := 1, end_ := 3 } == [(2 : UInt8), 3]

-- view bytes extracts a prefix slice.
#guard view__Bytes { s := [(1 : UInt8), 2, 3], beg := 0, end_ := 2 } == [(1 : UInt8), 2]

-- raw views are checked against the Dafny subtype validity condition.
#guard view__Valid? { s := [], beg := 0, end_ := 1 } == false

-- empty writer has empty bytes.
#guard writer__Bytes { length := 0, chain := Chain.empty } == []

-- Writer copy/to-array specs must keep the Dafny Unsaturated? precondition.
#guard writer__Unsaturated? { length := UInt32.ofNat (UInt32.size - 1), chain := Chain.empty } == false

-- string body lexer starts unescaped.
#guard stringBodyLexerStart == false

-- escaping leaves non-special characters alone.
#guard JSON.parametricEscaping_Escape ['a'] ['"'] '\\' == ['a']

-- escaping prefixes a special quote.
#guard JSON.parametricEscaping_Escape ['"'] ['"'] '\\' == ['\\', '"']

-- unescape inverts a simple escaped quote.
#guard
  match JSON.parametricEscaping_Unescape ['\\', '"'] '\\' with
  | .ok chars => chars == ['"']
  | .error _ => false

-- pushFast appends to a vector.
#guard (JSON.vector_PushFast { items := [1], capacity := 4, default_ := 0 } 2).items == [1, 2]

-- decimal conversion accumulates digits in the requested base.
#guard
  JSON.parametricConversion_ToNat_any
      ['1', '2']
      10
      [('0', 0), ('1', 1), ('2', 2), ('3', 3), ('4', 4),
       ('5', 5), ('6', 6), ('7', 7), ('8', 8), ('9', 9)] == 12

-- CopyTo overwrites exactly the selected region.
#guard
  JSON.view__CopyTo
      { s := [(7 : UInt8), 8], beg := 0, end_ := 2 }
      [(0 : UInt8), 0, 0, 0]
      1 == [(0 : UInt8), 7, 8, 0]

-- chain_CopyTo places chain bytes ending at the requested offset.
#guard
  JSON.chain_CopyTo
      (JSON.Chain.cons JSON.Chain.empty { s := [(7 : UInt8), 8], beg := 0, end_ := 2 })
      [(0 : UInt8), 0, 0, 0]
      2 == [(7 : UInt8), 8, 0, 0]

-- writer__Append extends bytes and saturated length.
#guard
  let w := JSON.writer__Append JSON.writer__Empty { s := [(7 : UInt8), 8], beg := 0, end_ := 2 }
  w.length == 2 && JSON.writer__Bytes w == [(7 : UInt8), 8]

-- writer__CopyTo writes accumulated bytes into the destination prefix.
#guard
  let w := JSON.writer__Append JSON.writer__Empty { s := [(7 : UInt8), 8], beg := 0, end_ := 2 }
  JSON.writer__CopyTo w [(0 : UInt8), 0, 0, 0] == [(7 : UInt8), 8, 0, 0]

-- writer__ToArray returns accumulated chain bytes.
#guard
  let w := JSON.writer__Append JSON.writer__Empty { s := [(7 : UInt8), 8], beg := 0, end_ := 2 }
  JSON.writer__ToArray w == [(7 : UInt8), 8]

-- stringBody accepts an unescaped quote and tracks a backslash escape.
#guard
  JSON.stringBody String false (some (34 : UInt8)) ==
    (JSON.LexerResult.accept : JSON.LexerResult JSON.StringBodyLexerState String)

#guard
  JSON.stringBody String false (some (92 : UInt8)) ==
    (JSON.LexerResult.partial_ true : JSON.LexerResult JSON.StringBodyLexerState String)

-- lexString enters the body after the opening quote and rejects other starts.
#guard
  JSON.lexString JSON.StringLexerState.start (some (34 : UInt8)) ==
    (JSON.LexerResult.partial_ (JSON.StringLexerState.body false) :
      JSON.LexerResult JSON.StringLexerState String)

#guard
  JSON.lexString JSON.StringLexerState.start (some (120 : UInt8)) ==
    (JSON.LexerResult.reject "String must start with double quote" :
      JSON.LexerResult JSON.StringLexerState String)

-- vector_Put updates an existing index.
#guard
  (JSON.vector_Put { items := [1, 2], capacity := 4, default_ := 0 } 1 9).items == [1, 9]

-- vector_Realloc grows capacity when requested.
#guard
  match JSON.vector_Realloc { items := [1, 2], capacity := 4, default_ := 0 } 8 with
  | .ok v => v.capacity == 8
  | .error _ => false

-- vector_PopFast removes the last element.
#guard
  (JSON.vector_PopFast { items := [1, 2], capacity := 4, default_ := 0 }).items == [1]

-- vector_ReallocDefault allocates capacity for an empty vector.
#guard
  match JSON.vector_ReallocDefault { items := ([] : List Nat), capacity := 0, default_ := 0 } with
  | .ok v => v.capacity == 1
  | .error _ => false

-- vector_Ensure grows enough capacity for reserved space.
#guard
  match JSON.vector_Ensure { items := [1, 2], capacity := 4, default_ := 0 } 3 with
  | .ok v => decide (5 ≤ v.capacity)
  | .error _ => false

-- vector_Push reallocates when the vector is full.
#guard
  match JSON.vector_Push { items := [1, 2], capacity := 2, default_ := 0 } 3 with
  | .ok v => v.items == [1, 2, 3] && v.capacity == 4
  | .error _ => false

-- serializer_string quotes UTF-8 bytes.
#guard
  match JSON.serializer_string "x" with
  | .ok bs => bs == [(34 : UInt8), 120, 34]
  | .error _ => false

-- serializer_string escapes embedded quotes.
#guard
  match JSON.serializer_string "a\"b" with
  | .ok bs => bs == [(34 : UInt8), 97, 92, 34, 98, 34]
  | .error _ => false

-- serializer_string escapes backslashes.
#guard
  match JSON.serializer_string "a\\b" with
  | .ok bs => bs == [(34 : UInt8), 97, 92, 92, 98, 34]
  | .error _ => false

-- serializer_string escapes JSON control characters.
#guard
  match JSON.serializer_string "a\n\tb" with
  | .ok bs => bs == [(34 : UInt8), 97, 92, 110, 92, 116, 98, 34]
  | .error _ => false

-- serializer_string renders unnamed control characters as \u00XX.
#guard
  match JSON.serializer_string (String.singleton (Char.ofNat 1)) with
  | .ok bs => bs == [(34 : UInt8), 92, 117, 48, 48, 48, 49, 34]
  | .error _ => false

-- serializer_number renders an integer decimal.
#guard
  match JSON.serializer_number { n := 12, e10 := 0 } with
  | .ok bs => bs == [(49 : UInt8), 50]
  | .error _ => false

-- serializer_keyValue composes key, colon, and value bytes.
#guard
  match JSON.serializer_keyValue ("a", JSON.JSON.null) with
  | .ok bs => bs == [(34 : UInt8), 97, 34, 58, 110, 117, 108, 108]
  | .error _ => false

-- serializer_keyValue escapes object keys.
#guard
  match JSON.serializer_keyValue ("a\"b", JSON.JSON.null) with
  | .ok bs => bs == [(34 : UInt8), 97, 92, 34, 98, 34, 58, 110, 117, 108, 108]
  | .error _ => false

-- serializer_json delegates to serializer_value.
#guard
  match JSON.serializer_json JSON.JSON.null with
  | .ok bs => bs == [(110 : UInt8), 117, 108, 108]
  | .error _ => false

-- high-level API serialization covers null.
#guard
  match JSON.apiSerializeAlloc JSON.JSON.null with
  | .ok bs => bs == [(110 : UInt8), 117, 108, 108]
  | .error _ => false

-- high-level API serialization preserves string payload bytes in the scoped model.
#guard
  match JSON.apiSerializeAlloc (JSON.JSON.string "x") with
  | .ok bs => bs == [(34 : UInt8), 120, 34]
  | .error _ => false

-- high-level API serialization escapes string payload bytes.
#guard
  match JSON.apiSerializeAlloc (JSON.JSON.string "a\nb") with
  | .ok bs => bs == [(34 : UInt8), 97, 92, 110, 98, 34]
  | .error _ => false

-- high-level API serialization escapes object keys through the object path.
#guard
  match JSON.apiSerializeAlloc (JSON.JSON.object [("a\"b", JSON.JSON.null)]) with
  | .ok bs => bs == [(123 : UInt8), 34, 97, 92, 34, 98, 34, 58, 110, 117, 108, 108, 125]
  | .error _ => false

-- nested object/array values have enough serializer fuel and keep escapes.
#guard
  match JSON.serializer_value (JSON.JSON.object [("xs", JSON.JSON.array [JSON.JSON.string "a\nb"])]) with
  | .ok bs => bs == [(123 : UInt8), 34, 120, 115, 34, 58, 91, 34, 97, 92, 110, 98, 34, 93, 125]
  | .error _ => false

private def guardView (bs : List UInt8) : JSON.View_ :=
  JSON.view__OfBytes bs

private def guardStructural {T : Type} (t : T) : JSON.Structural T :=
  { before := JSON.view__Empty, t := t, after := JSON.view__Empty }

private def guardStructuralWith {T : Type} (before : List UInt8) (t : T) (after : List UInt8) : JSON.Structural T :=
  { before := guardView before, t := t, after := guardView after }

private def guardString (bs : List UInt8) : JSON.jstring :=
  { lq := guardView [(34 : UInt8)], contents := guardView bs, rq := guardView [(34 : UInt8)] }

private def guardNumber (bs : List UInt8) : JSON.jnumber :=
  { minus := JSON.view__Empty, num := guardView bs, frac := none, exp := none }

private def guardEmptyObject : JSON.GrammarObject :=
  { inner :=
      { l := guardStructural (guardView [(123 : UInt8)]),
        data := [],
        r := guardStructural (guardView [(125 : UInt8)]) } }

private def guardInvalidOpenObject : JSON.GrammarObject :=
  { inner :=
      { l := guardStructural (guardView [(65 : UInt8)]),
        data := [],
        r := guardStructural (guardView [(125 : UInt8)]) } }

-- grammar validity restores the fixed-token refinements erased by `abbrev ... := View_`.
#guard JSON.jquote__Valid? (guardView [(34 : UInt8)]) == true

#guard JSON.jquote__Valid? (guardView [(65 : UInt8)]) == false

#guard JSON.je__Valid? (guardView [(69 : UInt8)]) == true

#guard JSON.jblanks__Valid? (guardView [(32 : UInt8), 10, 13, 9]) == true

#guard JSON.jblanks__Valid? (guardView [(65 : UInt8)]) == false

#guard JSON.jnumber__Valid? (guardNumber [(48 : UInt8)]) == true

#guard JSON.jnumber__Valid? (guardNumber [(48 : UInt8), 49]) == false

#guard JSON.jSON__Valid? (guardStructural (JSON.GrammarValue.object guardEmptyObject)) == true

#guard JSON.jSON__Valid? (guardStructural (JSON.GrammarValue.object guardInvalidOpenObject)) == false

#guard JSON.jSON__Valid? (guardStructural (JSON.GrammarValue.number (guardNumber [(48 : UInt8), 49]))) == false

-- comma-separated grammar sequences must not have a trailing suffix.
#guard
  let comma : JSON.Structural JSON.View_ := guardStructural (guardView [(44 : UInt8)])
  let arr : JSON.GrammarArray :=
    { inner :=
        { l := guardStructural (guardView [(91 : UInt8)]),
          data :=
            [ { t := JSON.GrammarValue.null (guardView [(110 : UInt8), 117, 108, 108]),
                suffix := JSON.Maybe.nonEmpty comma } ],
          r := guardStructural (guardView [(93 : UInt8)]) } }
  JSON.jSON__Valid? (guardStructural (JSON.GrammarValue.array arr)) == false

-- invalid grammar trees are rejected instead of being serialized as arbitrary bytes.
#guard
  match JSON.zcApiSerializeAlloc (guardStructural (JSON.GrammarValue.object guardInvalidOpenObject)) with
  | .ok _ => false
  | .error _ => true

#guard
  match JSON.zcApiSerializeAlloc (guardStructural (JSON.GrammarValue.number (guardNumber [(48 : UInt8), 49]))) with
  | .ok _ => false
  | .error _ => true

-- zero-copy API serialization preserves top-level surrounding views.
#guard
  match JSON.zcApiSerializeAlloc
      { before := guardView [(32 : UInt8)],
        t := JSON.GrammarValue.object guardEmptyObject,
        after := guardView [(10 : UInt8)] } with
  | .ok bs => bs == [(32 : UInt8), 123, 125, 10]
  | .error _ => false

-- zero-copy API serialization preserves key, colon spacing, and boolean payload bytes.
#guard
  let member : JSON.jKeyValue :=
    { k := guardString [(97 : UInt8)],
      colon := guardStructuralWith [] (guardView [(58 : UInt8)]) [(32 : UInt8)],
      v := JSON.GrammarValue.bool (guardView [(116 : UInt8), 114, 117, 101]) }
  let obj : JSON.GrammarObject :=
    { inner :=
        { l := guardStructural (guardView [(123 : UInt8)]),
          data := [{ t := member, suffix := JSON.Maybe.empty }],
          r := guardStructural (guardView [(125 : UInt8)]) } }
  match JSON.zcApiSerializeAlloc (guardStructural (JSON.GrammarValue.object obj)) with
  | .ok bs => bs == [(123 : UInt8), 34, 97, 34, 58, 32, 116, 114, 117, 101, 125]
  | .error _ => false

-- zero-copy API serialization traverses nested arrays and object values.
#guard
  let comma : JSON.Structural JSON.View_ := guardStructural (guardView [(44 : UInt8)])
  let arr : JSON.GrammarArray :=
    { inner :=
        { l := guardStructural (guardView [(91 : UInt8)]),
          data :=
            [ { t := JSON.GrammarValue.null (guardView [(110 : UInt8), 117, 108, 108]),
                suffix := JSON.Maybe.nonEmpty comma },
              { t := JSON.GrammarValue.object guardEmptyObject,
                suffix := JSON.Maybe.empty } ],
          r := guardStructural (guardView [(93 : UInt8)]) } }
  match JSON.zcApiSerializeAlloc (guardStructural (JSON.GrammarValue.array arr)) with
  | .ok bs => bs == [(91 : UInt8), 110, 117, 108, 108, 44, 123, 125, 93]
  | .error _ => false
