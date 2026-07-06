import JsonV2.Harness

/-!
# Json.Spec.ZeroCopy.API

Frozen specifications for `JSON.ZeroCopy.API`.

DO NOT MODIFY - this file is frozen curator-given content.
-/

/-- Zero-copy allocation succeeds on valid grammar trees and returns their concrete-syntax bytes. -/
def spec_zcApiSerializeAlloc_always_ok (impl : RepoImpl) : Prop :=
  ∀ (js : JSON.jSON),
    JSON.jSON__Valid? js = true →
    (JSON.zeroCopyJSONBytes js).length < UInt32.size →
    impl.json.zcApiSerializeAlloc js = .ok (JSON.zeroCopyJSONBytes js)

/-- Zero-copy allocation rejects grammar trees that violate concrete-token validity. -/
def spec_zcApiSerializeAlloc_rejects_invalid_grammar (impl : RepoImpl) : Prop :=
  ∀ (js : JSON.jSON),
    JSON.jSON__Valid? js = false →
    ∃ err, impl.json.zcApiSerializeAlloc js = .error err
