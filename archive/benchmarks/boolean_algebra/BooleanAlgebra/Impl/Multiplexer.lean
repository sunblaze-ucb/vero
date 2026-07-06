-- !benchmark @start imports
-- !benchmark @end imports

/-!
# BooleanAlgebra.Impl.Multiplexer

Scaffolded from `benchmark.json` via the python-from-json curation
stage. API signatures are extracted to `abbrev`s; bodies are `sorry`
stubs wrapped in `!benchmark code` markers for the LLM to fill.
-/

namespace BooleanAlgebra

-- ── API signatures (DO NOT MODIFY) ───────────────────────────
abbrev MuxSig := Int → Int → Int → Int

end BooleanAlgebra

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- !benchmark @start code_aux def=mux
-- !benchmark @end code_aux def=mux

def BooleanAlgebra.mux : BooleanAlgebra.MuxSig :=
-- !benchmark @start code def=mux
  fun input0 input1 select => if select = 0 then input0 else input1
-- !benchmark @end code def=mux
