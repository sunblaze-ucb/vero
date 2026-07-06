-- !benchmark @start imports
-- !benchmark @end imports

/-!
# BooleanAlgebra.Impl.OrGate

Scaffolded from `benchmark.json` via the python-from-json curation
stage. API signatures are extracted to `abbrev`s; bodies are `sorry`
stubs wrapped in `!benchmark code` markers for the LLM to fill.
-/

namespace BooleanAlgebra

-- ── API signatures (DO NOT MODIFY) ───────────────────────────
abbrev OrGateSig := Int → Int → Int

end BooleanAlgebra

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- !benchmark @start code_aux def=or_gate
-- !benchmark @end code_aux def=or_gate

def BooleanAlgebra.or_gate : BooleanAlgebra.OrGateSig :=
-- !benchmark @start code def=or_gate
  fun a b => if a = 1 ∨ b = 1 then 1 else 0
-- !benchmark @end code def=or_gate
