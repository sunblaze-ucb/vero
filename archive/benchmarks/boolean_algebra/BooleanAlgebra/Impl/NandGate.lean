-- !benchmark @start imports
-- !benchmark @end imports

/-!
# BooleanAlgebra.Impl.NandGate

Scaffolded from `benchmark.json` via the python-from-json curation
stage. API signatures are extracted to `abbrev`s; bodies are `sorry`
stubs wrapped in `!benchmark code` markers for the LLM to fill.
-/

namespace BooleanAlgebra

-- ── API signatures (DO NOT MODIFY) ───────────────────────────
abbrev NandGateSig := Int → Int → Int

end BooleanAlgebra

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- !benchmark @start code_aux def=nand_gate
-- !benchmark @end code_aux def=nand_gate

def BooleanAlgebra.nand_gate : BooleanAlgebra.NandGateSig :=
-- !benchmark @start code def=nand_gate
  fun a b => if a ≠ 0 ∧ b ≠ 0 then 0 else 1
-- !benchmark @end code def=nand_gate
