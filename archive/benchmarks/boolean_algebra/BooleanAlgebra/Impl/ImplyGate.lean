-- !benchmark @start imports
-- !benchmark @end imports

/-!
# BooleanAlgebra.Impl.ImplyGate

Scaffolded from `benchmark.json` via the python-from-json curation
stage. API signatures are extracted to `abbrev`s; bodies are `sorry`
stubs wrapped in `!benchmark code` markers for the LLM to fill.
-/

namespace BooleanAlgebra

-- ── API signatures (DO NOT MODIFY) ───────────────────────────
abbrev ImplyGateSig := Int → Int → Int
abbrev RecursiveImplyListSig := List Int → Int

end BooleanAlgebra

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- !benchmark @start code_aux def=imply_gate
-- !benchmark @end code_aux def=imply_gate

def BooleanAlgebra.imply_gate : BooleanAlgebra.ImplyGateSig :=
-- !benchmark @start code def=imply_gate
  fun a b => if a = 0 ∨ b = 1 then 1 else 0
-- !benchmark @end code def=imply_gate

-- !benchmark @start code_aux def=recursive_imply_list
partial def BooleanAlgebra.recursive_imply_list_aux : List Int → Int
  | [] => 0  -- ill-formed; matches Python's "raise ValueError" by returning 0
  | [_] => 0
  | a :: b :: rest =>
    let first := BooleanAlgebra.imply_gate a b
    match rest with
    | [] => first
    | _ => BooleanAlgebra.recursive_imply_list_aux (first :: rest)
-- !benchmark @end code_aux def=recursive_imply_list

def BooleanAlgebra.recursive_imply_list : BooleanAlgebra.RecursiveImplyListSig :=
-- !benchmark @start code def=recursive_imply_list
  BooleanAlgebra.recursive_imply_list_aux
-- !benchmark @end code def=recursive_imply_list
