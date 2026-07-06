-- !benchmark @start imports
-- !benchmark @end imports

/-!
# BooleanAlgebra.Impl.XnorGate

Scaffolded from `benchmark.json` via the python-from-json curation
stage. API signatures are extracted to `abbrev`s; bodies are `sorry`
stubs wrapped in `!benchmark code` markers for the LLM to fill.
-/

namespace BooleanAlgebra

-- ── API signatures (DO NOT MODIFY) ───────────────────────────
abbrev XnorGateSig := Int → Int → Int

end BooleanAlgebra

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- !benchmark @start code_aux def=xnor_gate
-- !benchmark @end code_aux def=xnor_gate

def BooleanAlgebra.xnor_gate : BooleanAlgebra.XnorGateSig :=
-- !benchmark @start code def=xnor_gate
  fun a b => if a = b then 1 else 0
-- !benchmark @end code def=xnor_gate
