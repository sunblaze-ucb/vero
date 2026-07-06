import JsonV2.Harness

/-!
# Json.Spec.Utils.Str

Frozen specifications for string utilities from `JSON.Utils.Str`.
-/

/-- The converted natural number is bounded by `base ^ str.length` when all digits are below the base. -/
def spec_parametricConversion_ToNat_bound (impl : RepoImpl) : Prop :=
  ∀ (str : List Char) (base : Nat) (digits : List (Char × Nat)),
  base > 0 →
  (∀ c ∈ str, ∃ p ∈ digits, p.1 = c) →
  (∀ c ∈ str, ∀ p ∈ digits, p.1 = c → p.2 < base) →
  impl.json.parametricConversion_ToNat_any str base digits < base ^ str.length

/-- Escaping and then unescaping with the same escape character recovers the original string. -/
def spec_parametricEscaping_Unescape_Escape (impl : RepoImpl) : Prop :=
  ∀ (str : List Char) (special : List Char) (esc : Char),
  esc ∈ special →
  impl.json.parametricEscaping_Unescape (impl.json.parametricEscaping_Escape str special esc) esc = .ok str

/-- Concatenation agrees with joining by the empty separator. -/
def spec_concat_Join (impl : RepoImpl) : Prop :=
  ∀ (strs : List String), impl.json.concat strs = impl.json.join "" strs
