import JsonV2.Harness

/-!
# Json.Spec.API

Frozen specifications for `JSON.API`.

DO NOT MODIFY - this file is frozen curator-given content.
-/

/-- serialize alloc null ok -/
def spec_serialize_alloc_null_ok (impl : RepoImpl) : Prop :=
  ∃ bs : List UInt8, impl.json.apiSerializeAlloc JSON.JSON.null = .ok bs ∧ bs ≠ []

/-- serialize alloc bool ok -/
def spec_serialize_alloc_bool_ok (impl : RepoImpl) : Prop :=
  ∀ (b : Bool), ∃ bs : List UInt8,
    impl.json.apiSerializeAlloc (JSON.JSON.bool b) = .ok bs ∧ bs ≠ []
