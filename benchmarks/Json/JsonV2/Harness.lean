import JsonV2.Bundle

/-!
# Json.Harness

Benchmark harness: `RepoImpl` structure, canonical implementation wiring,
and the `joint_unsat` macro consumed by downstream proof generation.

DO NOT MODIFY - benchmark infrastructure.
-/

structure RepoImpl where
  json : JsonV2Bundle

noncomputable def canonical : RepoImpl where
  json := {
    parametricConversion_ToNat_any := JSON.parametricConversion_ToNat_any
    parametricEscaping_Escape := JSON.parametricEscaping_Escape
    parametricEscaping_Unescape := JSON.parametricEscaping_Unescape
    join := JSON.join
    concat := JSON.concat
    view__CopyTo := JSON.view__CopyTo
    chain_CopyTo := JSON.chain_CopyTo
    writer__Append := JSON.writer__Append
    writer__CopyTo := JSON.writer__CopyTo
    writer__ToArray := JSON.writer__ToArray
    stringBody := JSON.stringBody
    lexString := JSON.lexString
    vector_Put := JSON.vector_Put
    vector_Realloc := JSON.vector_Realloc
    vector_PopFast := JSON.vector_PopFast
    vector_PushFast := JSON.vector_PushFast
    vector_ReallocDefault := JSON.vector_ReallocDefault
    vector_Ensure := JSON.vector_Ensure
    vector_Push := JSON.vector_Push
    intToBytes := JSON.intToBytes
    serializer_bool := JSON.serializer_bool
    serializer_string := JSON.serializer_string
    serializer_int := JSON.serializer_int
    serializer_number := JSON.serializer_number
    serializer_object := JSON.serializer_object
    serializer_array := JSON.serializer_array
    serializer_value := JSON.serializer_value
    serializer_keyValue := JSON.serializer_keyValue
    serializer_json := JSON.serializer_json
    zcApiSerializeAlloc := JSON.zcApiSerializeAlloc
    apiSerializeAlloc := JSON.apiSerializeAlloc
  }

/--
`joint_unsat spec_A spec_B [spec_C ...] by <proof>` generates a theorem
that no implementation satisfies all listed specs simultaneously.
-/
syntax "joint_unsat" ident ident ident* "by" tacticSeq : command

open Lean in
macro_rules
  | `(joint_unsat $s1 $s2 $[$rest]* by $proof) => do
    let specs := #[s1, s2] ++ rest
    let name := specs.foldl (init := `joint_unsat) fun acc s => Name.append acc s.getId
    let mut body ← `($(specs[0]!) impl)
    for s in specs[1:] do
      body ← `($body ∧ $s impl)
    `(theorem $(mkIdent name) : ¬ ∃ impl : RepoImpl, $body := by $proof)
