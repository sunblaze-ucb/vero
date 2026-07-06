import JsonV2.Harness

/-!
# Json.Spec.Serializer

Frozen specifications for `JSON.Serializer`.
-/

open JSON

/-- Serializer emits the JSON literal `true` for boolean true. -/
def spec_serializer_bool_true (impl : RepoImpl) : Prop :=
  impl.json.serializer_bool true = [116, 114, 117, 101]

/-- Serializer emits the JSON literal `false` for boolean false. -/
def spec_serializer_bool_false (impl : RepoImpl) : Prop :=
  impl.json.serializer_bool false = [102, 97, 108, 115, 101]

/-- Serializer emits the ASCII digit zero for integer zero. -/
def spec_serializer_int_zero (impl : RepoImpl) : Prop :=
  impl.json.serializer_int 0 = .ok [48]

/-- Successful integer serialization emits only ASCII sign and decimal digit bytes. -/
def spec_serializer_int_ascii (impl : RepoImpl) : Prop :=
  ∀ (n : Int) (bs : serializerBytes),
    impl.json.serializer_int n = .ok bs →
    ∀ b ∈ bs, b.toNat = 45 ∨ (48 ≤ b.toNat ∧ b.toNat ≤ 57)

/-- Successful string serialization wraps exactly the JSON-escaped UTF-8 payload. -/
def spec_serializer_string_quotes (impl : RepoImpl) : Prop :=
  ∀ (s : String) (esc : serializerBytes),
    jsonEscapeToUTF8 s = .ok esc →
    esc.length < 2 ^ 32 →
    impl.json.serializer_string s = .ok ([34] ++ esc ++ [34])

/-- If the escaped UTF-8 payload for a string is too long, serializer_string reports stringTooLong. -/
def spec_serializer_string_too_long (impl : RepoImpl) : Prop :=
  ∀ (s : String) (esc : List UInt8),
    jsonEscapeToUTF8 s = .ok esc →
    esc.length ≥ 2 ^ 32 →
    impl.json.serializer_string s = .error (.stringTooLong s)

/-- Serializer emits the JSON literal `null` for null values. -/
def spec_serializer_value_null (impl : RepoImpl) : Prop :=
  impl.json.serializer_value JSON.null = .ok [110, 117, 108, 108]

/-- Value serialization delegates boolean values to serializer_bool. -/
def spec_serializer_value_bool (impl : RepoImpl) : Prop :=
  ∀ (b : Bool),
    impl.json.serializer_value (JSON.bool b) = .ok (impl.json.serializer_bool b)

/-- Value serialization delegates string values to serializer_string. -/
def spec_serializer_value_string (impl : RepoImpl) : Prop :=
  ∀ (s : String),
    impl.json.serializer_value (JSON.string s) = impl.json.serializer_string s

/-- Value serialization delegates numeric values to serializer_number. -/
def spec_serializer_value_number (impl : RepoImpl) : Prop :=
  ∀ (d : Decimal),
    impl.json.serializer_value (JSON.number d) = impl.json.serializer_number d

/-- Serializer emits an empty JSON array for the empty list. -/
def spec_serializer_array_empty (impl : RepoImpl) : Prop :=
  impl.json.serializer_array [] = .ok [91, 93]

/-- Serializer emits an empty JSON object for the empty key-value list. -/
def spec_serializer_object_empty (impl : RepoImpl) : Prop :=
  impl.json.serializer_object [] = .ok [123, 125]

/-- Complete JSON serialization is value serialization. -/
def spec_serializer_json_eq_value (impl : RepoImpl) : Prop :=
  ∀ (js : JSON),
    impl.json.serializer_json js = impl.json.serializer_value js

/-- KeyValue serialization composes the serialized key, colon byte, and serialized value. -/
def spec_serializer_keyValue_composes_string_colon_value (impl : RepoImpl) : Prop :=
  ∀ (k : String) (v : JSON) (kb vb : serializerBytes),
    impl.json.serializer_string k = .ok kb →
    impl.json.serializer_value v = .ok vb →
    impl.json.serializer_keyValue (k, v) = .ok (kb ++ [(58 : UInt8)] ++ vb)
