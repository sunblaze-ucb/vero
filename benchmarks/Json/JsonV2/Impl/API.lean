import JsonV2.Impl.Values
import JsonV2.Impl.Errors
import JsonV2.Impl.Serializer

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Json.Impl.API

High-level JSON API entry points translated from `JSON.API`.

DO NOT MODIFY types or signatures - these are the fixed vocabulary.
Implement only the function bodies.
-/

namespace JSON

-- API signatures (no markers - fixed vocabulary)

abbrev ApiSerializeAllocSig := JSON → SerializationResult (List UInt8)

end JSON

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- !benchmark @start code_aux def=apiSerializeAlloc
-- !benchmark @end code_aux def=apiSerializeAlloc

def JSON.apiSerializeAlloc : JSON.ApiSerializeAllocSig :=
-- !benchmark @start code def=apiSerializeAlloc
  JSON.serializer_json
-- !benchmark @end code def=apiSerializeAlloc
