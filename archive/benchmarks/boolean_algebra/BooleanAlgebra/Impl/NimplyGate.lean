-- !benchmark @start imports
-- !benchmark @end imports

/-!
# BooleanAlgebra.Impl.NimplyGate

Scaffolded from `benchmark.json` via the python-from-json curation
stage. API signatures are extracted to `abbrev`s; bodies are `sorry`
stubs wrapped in `!benchmark code` markers for the LLM to fill.
-/

namespace BooleanAlgebra

-- ── API signatures (DO NOT MODIFY) ───────────────────────────
abbrev NimplyGateSig := Int → Int → Int

end BooleanAlgebra

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- !benchmark @start code_aux def=nimply_gate
-- !benchmark @end code_aux def=nimply_gate

def BooleanAlgebra.nimply_gate : BooleanAlgebra.NimplyGateSig :=
-- !benchmark @start code def=nimply_gate
  fun a b => if a = 1 ∧ b = 0 then 1 else 0
-- !benchmark @end code def=nimply_gate
