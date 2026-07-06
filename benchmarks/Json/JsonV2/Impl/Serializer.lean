import JsonV2.Impl.Values
import JsonV2.Impl.Errors
import JsonV2.Impl.Spec

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Json.Impl.Serializer

Serialization reference implementations translated from `JSON.Serializer`.

DO NOT MODIFY types or signatures - these are the fixed vocabulary.
Implement only the function bodies.
-/

namespace JSON

-- Types (no markers - fixed vocabulary)

abbrev serializerResult (T : Type) := SerializationResult T

abbrev serializerBytes := List UInt8

-- Spec helpers (no markers - fixed vocabulary)

def jsonHexNibbleByte (n : Nat) : UInt8 :=
  UInt8.ofNat (if n < 10 then 48 + n else 55 + n)

def jsonEscapeByte (b : UInt8) : List UInt8 :=
  let n := b.toNat
  if n = 34 then
    [(92 : UInt8), 34]
  else if n = 92 then
    [(92 : UInt8), 92]
  else if n = 8 then
    [(92 : UInt8), 98]
  else if n = 12 then
    [(92 : UInt8), 102]
  else if n = 10 then
    [(92 : UInt8), 110]
  else if n = 13 then
    [(92 : UInt8), 114]
  else if n = 9 then
    [(92 : UInt8), 116]
  else if n < 32 then
    [(92 : UInt8), 117, 48, 48, jsonHexNibbleByte (n / 16), jsonHexNibbleByte (n % 16)]
  else
    [b]

def jsonEscapeBytes : List UInt8 → List UInt8
  | [] => []
  | b :: bs => jsonEscapeByte b ++ jsonEscapeBytes bs

def jsonEscapeToUTF8 (s : String) : SerializationResult (List UInt8) :=
  .ok (jsonEscapeBytes s.toUTF8.toList)

mutual
  @[simp]
  def serializerJsonSize : JSON → Nat
    | .null => 1
    | .bool _ => 1
    | .string _ => 1
    | .number _ => 1
    | .object obj => serializerKVListSize obj + 2
    | .array arr => serializerJSONListSize arr + 2

  @[simp]
  def serializerJSONListSize : List JSON → Nat
    | [] => 0
    | js :: rest => serializerJsonSize js + serializerJSONListSize rest + 1

  @[simp]
  def serializerKVListSize : List (String × JSON) → Nat
    | [] => 0
    | kv :: rest => serializerJsonSize kv.2 + serializerKVListSize rest + 2
end

-- API signatures (no markers - fixed vocabulary)

abbrev SerializerBoolSig := Bool → serializerBytes

abbrev SerializerStringSig := String → serializerResult serializerBytes

abbrev SerializerIntSig := Int → serializerResult serializerBytes

abbrev SerializerNumberSig := Decimal → serializerResult serializerBytes

abbrev SerializerObjectSig := List (String × JSON) → serializerResult serializerBytes

abbrev SerializerArraySig := List JSON → serializerResult serializerBytes

abbrev SerializerValueSig := JSON → serializerResult serializerBytes

abbrev SerializerKeyValueSig := String × JSON → serializerResult serializerBytes

abbrev SerializerJsonSig := JSON → serializerResult serializerBytes

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- !benchmark @start code_aux def=serializer_bool
-- !benchmark @end code_aux def=serializer_bool

def serializer_bool : SerializerBoolSig :=
-- !benchmark @start code def=serializer_bool
  fun b =>
    if b then
      [116, 114, 117, 101]
    else
      [102, 97, 108, 115, 101]
-- !benchmark @end code def=serializer_bool

-- !benchmark @start code_aux def=serializer_string
-- !benchmark @end code_aux def=serializer_string

def serializer_string : SerializerStringSig :=
-- !benchmark @start code def=serializer_string
  fun s =>
    match jsonEscapeToUTF8 s with
    | .error err => .error err
    | .ok esc =>
      if esc.length ≥ 2 ^ 32 then
        .error (.stringTooLong s)
      else
        .ok ([34] ++ esc ++ [34])
-- !benchmark @end code def=serializer_string

-- !benchmark @start code_aux def=serializer_int
-- !benchmark @end code_aux def=serializer_int

def serializer_int : SerializerIntSig :=
-- !benchmark @start code def=serializer_int
  fun n =>
    let bs := intDecimalBytes n
    if bs.length ≥ 2 ^ 32 then
      .error (.intTooLarge n)
    else
      .ok bs
-- !benchmark @end code def=serializer_int

-- !benchmark @start code_aux def=serializer_number
-- !benchmark @end code_aux def=serializer_number

def serializer_number : SerializerNumberSig :=
-- !benchmark @start code def=serializer_number
  fun dec =>
    let sign : serializerBytes := if dec.n < 0 then [45] else []
    match serializer_int (Int.ofNat dec.n.natAbs) with
    | .error err => .error err
    | .ok num =>
      if dec.e10 = 0 then
        .ok (sign ++ num)
      else
        let expSign : serializerBytes := if dec.e10 < 0 then [45] else []
        match serializer_int (Int.ofNat dec.e10.natAbs) with
        | .error err => .error err
        | .ok exp => .ok (sign ++ num ++ [101] ++ expSign ++ exp)
-- !benchmark @end code def=serializer_number

mutual

@[simp]
def serializer_objectItemsFuel : Nat → List (String × JSON) → serializerResult serializerBytes
  | 0, [] => .ok []
  | 0, _ :: _ => .error .outOfMemory
  | _fuel + 1, [] => .ok []
  | fuel + 1, [kv] => serializer_keyValueFuel fuel kv
  | fuel + 1, kv :: rest =>
    match serializer_keyValueFuel fuel kv with
    | .error err => .error err
    | .ok head =>
      match serializer_objectItemsFuel fuel rest with
      | .error err => .error err
      | .ok tail => .ok (head ++ [44] ++ tail)

@[simp]
def serializer_objectFuel : Nat → List (String × JSON) → serializerResult serializerBytes
  | 0, _ => .error .outOfMemory
  | fuel + 1, obj =>
    match serializer_objectItemsFuel fuel obj with
    | .error err => .error err
    | .ok bs => .ok ([123] ++ bs ++ [125])

@[simp]
def serializer_arrayItemsFuel : Nat → List JSON → serializerResult serializerBytes
  | 0, [] => .ok []
  | 0, _ :: _ => .error .outOfMemory
  | _fuel + 1, [] => .ok []
  | fuel + 1, [js] => serializer_valueFuel fuel js
  | fuel + 1, js :: rest =>
    match serializer_valueFuel fuel js with
    | .error err => .error err
    | .ok head =>
      match serializer_arrayItemsFuel fuel rest with
      | .error err => .error err
      | .ok tail => .ok (head ++ [44] ++ tail)

@[simp]
def serializer_arrayFuel : Nat → List JSON → serializerResult serializerBytes
  | 0, _ => .error .outOfMemory
  | fuel + 1, arr =>
    match serializer_arrayItemsFuel fuel arr with
    | .error err => .error err
    | .ok bs => .ok ([91] ++ bs ++ [93])

@[simp]
def serializer_valueFuel : Nat → JSON → serializerResult serializerBytes
  | 0, _ => .error .outOfMemory
  | _fuel + 1, .null => .ok [110, 117, 108, 108]
  | _fuel + 1, .bool b => .ok (serializer_bool b)
  | _fuel + 1, .string s => serializer_string s
  | _fuel + 1, .number dec => serializer_number dec
  | fuel + 1, .object obj => serializer_objectFuel fuel obj
  | fuel + 1, .array arr => serializer_arrayFuel fuel arr

@[simp]
def serializer_keyValueFuel : Nat → String × JSON → serializerResult serializerBytes
  | 0, _ => .error .outOfMemory
  | fuel + 1, kv =>
    match serializer_string kv.1 with
    | .error err => .error err
    | .ok key =>
      match serializer_valueFuel fuel kv.2 with
      | .error err => .error err
      | .ok value => .ok (key ++ [(58 : UInt8)] ++ value)

-- !benchmark @start code_aux def=serializer_object
-- !benchmark @end code_aux def=serializer_object

def serializer_object : SerializerObjectSig :=
-- !benchmark @start code def=serializer_object
  fun obj => serializer_objectFuel (serializerKVListSize obj + 1) obj
-- !benchmark @end code def=serializer_object

-- !benchmark @start code_aux def=serializer_array
-- !benchmark @end code_aux def=serializer_array

def serializer_array : SerializerArraySig :=
-- !benchmark @start code def=serializer_array
  fun arr => serializer_arrayFuel (serializerJSONListSize arr + 1) arr
-- !benchmark @end code def=serializer_array

-- !benchmark @start code_aux def=serializer_value
-- !benchmark @end code_aux def=serializer_value

def serializer_value : SerializerValueSig :=
-- !benchmark @start code def=serializer_value
  fun js => serializer_valueFuel (serializerJsonSize js) js
-- !benchmark @end code def=serializer_value

-- !benchmark @start code_aux def=serializer_keyValue
-- !benchmark @end code_aux def=serializer_keyValue

def serializer_keyValue : SerializerKeyValueSig :=
-- !benchmark @start code def=serializer_keyValue
  fun kv =>
    match serializer_string kv.1 with
    | .error err => .error err
    | .ok key =>
      match serializer_value kv.2 with
      | .error err => .error err
      | .ok value => .ok (key ++ [(58 : UInt8)] ++ value)
-- !benchmark @end code def=serializer_keyValue

end

-- !benchmark @start code_aux def=serializer_json
-- !benchmark @end code_aux def=serializer_json

def serializer_json : SerializerJsonSig :=
-- !benchmark @start code def=serializer_json
  fun js => serializer_value js
-- !benchmark @end code def=serializer_json

end JSON
