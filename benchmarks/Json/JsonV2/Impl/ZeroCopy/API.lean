import JsonV2.Impl.Errors
import JsonV2.Impl.Grammar
import JsonV2.Impl.ConcreteSyntax.Spec

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Json.Impl.ZeroCopy.API

Zero-copy JSON API entry points translated from `JSON.ZeroCopy.API`.

DO NOT MODIFY types or signatures - these are the fixed vocabulary.
Implement only the function bodies.
-/

namespace JSON

-- Spec helpers (no markers - fixed vocabulary)

def zeroCopyJSONBytes (js : jSON) : List UInt8 := csStructural csValue js

-- API signatures (no markers - fixed vocabulary)

abbrev ZCApiSerializeAllocSig := jSON → SerializationResult (List UInt8)

end JSON

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- !benchmark @start code_aux def=zcApiSerializeAlloc
-- !benchmark @end code_aux def=zcApiSerializeAlloc

def JSON.zcApiSerializeAlloc : JSON.ZCApiSerializeAllocSig :=
-- !benchmark @start code def=zcApiSerializeAlloc
  fun js =>
    if JSON.jSON__Valid? js then
      .ok (JSON.zeroCopyJSONBytes js)
    else
      .error .invalidUnicode
-- !benchmark @end code def=zcApiSerializeAlloc
