-- !benchmark @start imports
-- !benchmark @end imports

/-!
# BooleanAlgebra.Impl.NotGate

Scaffolded from `benchmark.json` via the python-from-json curation
stage. API signatures are extracted to `abbrev`s; bodies are `sorry`
stubs wrapped in `!benchmark code` markers for the LLM to fill.
-/

namespace BooleanAlgebra

-- ── API signatures (DO NOT MODIFY) ───────────────────────────
abbrev NotGateSig := Int → Int

end BooleanAlgebra

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- !benchmark @start code_aux def=not_gate
-- !benchmark @end code_aux def=not_gate

def BooleanAlgebra.not_gate : BooleanAlgebra.NotGateSig :=
-- !benchmark @start code def=not_gate
  fun a => if a = 0 then 1 else 0
-- !benchmark @end code def=not_gate
