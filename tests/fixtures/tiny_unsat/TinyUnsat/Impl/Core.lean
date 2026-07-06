-- !benchmark @start imports
-- !benchmark @end imports

/-!
# TinyUnsat.Impl.Core

One API: ``answer : Nat``. Types + signature frozen; the body is the
curator's reference impl (pipeline replaces it with ``sorry`` before
presenting the benchmark to the LLM).
-/

namespace TU

-- ── API signature (DO NOT MODIFY) ─────────────────────────────
abbrev AnswerSig := Nat

end TU

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- !benchmark @start code_aux def=answer
-- !benchmark @end code_aux def=answer

def TU.answer : TU.AnswerSig :=
-- !benchmark @start code def=answer
  1
-- !benchmark @end code def=answer
