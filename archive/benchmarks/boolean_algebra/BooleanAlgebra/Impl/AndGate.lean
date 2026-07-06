-- !benchmark @start imports
-- !benchmark @end imports

/-!
# BooleanAlgebra.Impl.AndGate

Scaffolded from `benchmark.json` via the python-from-json curation
stage. API signatures are extracted to `abbrev`s; bodies are `sorry`
stubs wrapped in `!benchmark code` markers for the LLM to fill.
-/

namespace BooleanAlgebra

-- ── API signatures (DO NOT MODIFY) ───────────────────────────
abbrev AndGateSig := Int → Int → Int
abbrev NInputAndGateSig := List Int → Int

end BooleanAlgebra

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- !benchmark @start code_aux def=and_gate
-- !benchmark @end code_aux def=and_gate

def BooleanAlgebra.and_gate : BooleanAlgebra.AndGateSig :=
-- !benchmark @start code def=and_gate
  fun a b => if a = 0 then 0 else b
-- !benchmark @end code def=and_gate

-- !benchmark @start code_aux def=n_input_and_gate
-- !benchmark @end code_aux def=n_input_and_gate

def BooleanAlgebra.n_input_and_gate : BooleanAlgebra.NInputAndGateSig :=
-- !benchmark @start code def=n_input_and_gate
  fun xs => if xs.all (· ≠ 0) then 1 else 0
-- !benchmark @end code def=n_input_and_gate
