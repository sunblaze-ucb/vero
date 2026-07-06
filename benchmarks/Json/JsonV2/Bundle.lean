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
# Json.Bundle

Per-package implementation bundle for the JSON benchmark.

DO NOT MODIFY - benchmark infrastructure.
-/

structure JsonV2Bundle where
  parametricConversion_ToNat_any : JSON.ParametricConversion_ToNat_anySig
  parametricEscaping_Escape : JSON.ParametricEscaping_EscapeSig
  parametricEscaping_Unescape : JSON.ParametricEscaping_UnescapeSig
  join : JSON.JoinSig
  concat : JSON.ConcatSig
  view__CopyTo : JSON.View_CopyToSig
  chain_CopyTo : JSON.ChainCopyToSig
  writer__Append : JSON.WriterAppendSig
  writer__CopyTo : JSON.WriterCopyToSig
  writer__ToArray : JSON.WriterToArraySig
  stringBody : JSON.StringBodySig
  lexString : JSON.LexStringSig
  vector_Put : JSON.VectorPutSig
  vector_Realloc : JSON.VectorReallocSig
  vector_PopFast : JSON.VectorPopFastSig
  vector_PushFast : JSON.VectorPushFastSig
  vector_ReallocDefault : JSON.VectorReallocDefaultSig
  vector_Ensure : JSON.VectorEnsureSig
  vector_Push : JSON.VectorPushSig
  intToBytes : JSON.IntToBytesSig
  serializer_bool : JSON.SerializerBoolSig
  serializer_string : JSON.SerializerStringSig
  serializer_int : JSON.SerializerIntSig
  serializer_number : JSON.SerializerNumberSig
  serializer_object : JSON.SerializerObjectSig
  serializer_array : JSON.SerializerArraySig
  serializer_value : JSON.SerializerValueSig
  serializer_keyValue : JSON.SerializerKeyValueSig
  serializer_json : JSON.SerializerJsonSig
  zcApiSerializeAlloc : JSON.ZCApiSerializeAllocSig
  apiSerializeAlloc : JSON.ApiSerializeAllocSig
