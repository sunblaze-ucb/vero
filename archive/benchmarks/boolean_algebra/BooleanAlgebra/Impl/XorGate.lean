-- !benchmark @start imports
-- !benchmark @end imports

/-!
# BooleanAlgebra.Impl.XorGate

Scaffolded from `benchmark.json` via the python-from-json curation
stage. API signatures are extracted to `abbrev`s; bodies are `sorry`
stubs wrapped in `!benchmark code` markers for the LLM to fill.
-/

namespace BooleanAlgebra

-- ── API signatures (DO NOT MODIFY) ───────────────────────────
abbrev XorGateSig := Int → Int → Int

end BooleanAlgebra

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- !benchmark @start code_aux def=xor_gate
-- !benchmark @end code_aux def=xor_gate

def BooleanAlgebra.xor_gate : BooleanAlgebra.XorGateSig :=
-- !benchmark @start code def=xor_gate
  fun a b =>
    let zeros := (if a = 0 then 1 else 0) + (if b = 0 then 1 else 0)
    zeros % 2
-- !benchmark @end code def=xor_gate
