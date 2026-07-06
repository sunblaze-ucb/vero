import VestV2.Impl.RegularUints
import VestV2.Impl.RegularBytes

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# VestV2.Impl.RegularClone

Clone operations for VestV2 parser/serializer combinators. Each clone
function returns an identical copy of the given combinator. Unit-struct
combinators (U8, U16Le, U32Le, U64Le, Tail, Fixed) have trivially
reflexive clones; Variable copies its `n` field.

Types `Variable`, `Fixed`, `Tail` are imported from `RegularBytes`.
Types `U8`, `U16Le`, `U32Le`, `U64Le` are imported from `RegularUints`.

Types and signatures are fixed vocabulary (DO NOT MODIFY). Function
bodies are the curator's reference implementations; the pipeline
replaces them with `sorry` inside the `code` markers before presenting
the benchmark to the LLM.
-/

namespace VestV2

-- ── API signatures (DO NOT MODIFY) ───────────────────────

abbrev CloneU8Sig := U8 → U8
abbrev CloneU16LeSig := U16Le → U16Le
abbrev CloneU32LeSig := U32Le → U32Le
abbrev CloneU64LeSig := U64Le → U64Le
abbrev CloneTailSig := Tail → Tail
abbrev CloneVariableSig := Variable → Variable
abbrev CloneFixedSig := Fixed → Fixed

end VestV2

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- ── Implementation stubs (LLM task) ────────────────────────

-- !benchmark @start code_aux def=cloneU8
-- !benchmark @end code_aux def=cloneU8

def VestV2.cloneU8 : VestV2.CloneU8Sig :=
-- !benchmark @start code def=cloneU8
  fun x => x
-- !benchmark @end code def=cloneU8

-- !benchmark @start code_aux def=cloneU16Le
-- !benchmark @end code_aux def=cloneU16Le

def VestV2.cloneU16Le : VestV2.CloneU16LeSig :=
-- !benchmark @start code def=cloneU16Le
  fun x => x
-- !benchmark @end code def=cloneU16Le

-- !benchmark @start code_aux def=cloneU32Le
-- !benchmark @end code_aux def=cloneU32Le

def VestV2.cloneU32Le : VestV2.CloneU32LeSig :=
-- !benchmark @start code def=cloneU32Le
  fun x => x
-- !benchmark @end code def=cloneU32Le

-- !benchmark @start code_aux def=cloneU64Le
-- !benchmark @end code_aux def=cloneU64Le

def VestV2.cloneU64Le : VestV2.CloneU64LeSig :=
-- !benchmark @start code def=cloneU64Le
  fun x => x
-- !benchmark @end code def=cloneU64Le

-- !benchmark @start code_aux def=cloneTail
-- !benchmark @end code_aux def=cloneTail

def VestV2.cloneTail : VestV2.CloneTailSig :=
-- !benchmark @start code def=cloneTail
  fun x => x
-- !benchmark @end code def=cloneTail

-- !benchmark @start code_aux def=cloneVariable
-- !benchmark @end code_aux def=cloneVariable

def VestV2.cloneVariable : VestV2.CloneVariableSig :=
-- !benchmark @start code def=cloneVariable
  fun x => ⟨x.n⟩
-- !benchmark @end code def=cloneVariable

-- !benchmark @start code_aux def=cloneFixed
-- !benchmark @end code_aux def=cloneFixed

def VestV2.cloneFixed : VestV2.CloneFixedSig :=
-- !benchmark @start code def=cloneFixed
  fun x => x
-- !benchmark @end code def=cloneFixed
