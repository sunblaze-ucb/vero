import BankLedger.Harness
import BankLedger.Spec.Account

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# BankLedger.Proof_modeproof.Account (illustration — `proof` mode)

Per-module proof file for the proof-only evaluation mode. Deterministic
from `Spec/Account.lean`: for each `spec_*` in the sibling Spec file,
the curator emits a pair `prove_<spec>` / `disprove_<spec>`.

The LLM fills exactly one of each pair; the other stays as `sorry`.
No `Proof/Joint.lean`, no anti-cheat macros consumed in this mode —
`canonical` is given (reference impl) and the LLM only proves over it.

Illustrative file, not imported by the root hub.
-/

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- ── spec_create_zero_balance ─────────────────────────────────

-- !benchmark @start proof_aux def=prove_create_zero_balance
-- !benchmark @end proof_aux def=prove_create_zero_balance

theorem prove_create_zero_balance : spec_create_zero_balance canonical := by
-- !benchmark @start proof def=prove_create_zero_balance kind=prove target=spec_create_zero_balance
  sorry
-- !benchmark @end proof def=prove_create_zero_balance

-- !benchmark @start proof_aux def=disprove_create_zero_balance
-- !benchmark @end proof_aux def=disprove_create_zero_balance

theorem disprove_create_zero_balance : ¬ spec_create_zero_balance canonical := by
-- !benchmark @start proof def=disprove_create_zero_balance kind=disprove target=spec_create_zero_balance
  sorry
-- !benchmark @end proof def=disprove_create_zero_balance

-- ── spec_create_exists ───────────────────────────────────────

-- !benchmark @start proof_aux def=prove_create_exists
-- !benchmark @end proof_aux def=prove_create_exists

theorem prove_create_exists : spec_create_exists canonical := by
-- !benchmark @start proof def=prove_create_exists kind=prove target=spec_create_exists
  sorry
-- !benchmark @end proof def=prove_create_exists

-- !benchmark @start proof_aux def=disprove_create_exists
-- !benchmark @end proof_aux def=disprove_create_exists

theorem disprove_create_exists : ¬ spec_create_exists canonical := by
-- !benchmark @start proof def=disprove_create_exists kind=disprove target=spec_create_exists
  sorry
-- !benchmark @end proof def=disprove_create_exists

-- ── spec_close_removes ───────────────────────────────────────

-- !benchmark @start proof_aux def=prove_close_removes
-- !benchmark @end proof_aux def=prove_close_removes

theorem prove_close_removes : spec_close_removes canonical := by
-- !benchmark @start proof def=prove_close_removes kind=prove target=spec_close_removes
  sorry
-- !benchmark @end proof def=prove_close_removes

-- !benchmark @start proof_aux def=disprove_close_removes
-- !benchmark @end proof_aux def=disprove_close_removes

theorem disprove_close_removes : ¬ spec_close_removes canonical := by
-- !benchmark @start proof def=disprove_close_removes kind=disprove target=spec_close_removes
  sorry
-- !benchmark @end proof def=disprove_close_removes

-- ── spec_close_preserves_others ──────────────────────────────

-- !benchmark @start proof_aux def=prove_close_preserves_others
-- !benchmark @end proof_aux def=prove_close_preserves_others

theorem prove_close_preserves_others : spec_close_preserves_others canonical := by
-- !benchmark @start proof def=prove_close_preserves_others kind=prove target=spec_close_preserves_others
  sorry
-- !benchmark @end proof def=prove_close_preserves_others

-- !benchmark @start proof_aux def=disprove_close_preserves_others
-- !benchmark @end proof_aux def=disprove_close_preserves_others

theorem disprove_close_preserves_others : ¬ spec_close_preserves_others canonical := by
-- !benchmark @start proof def=disprove_close_preserves_others kind=disprove target=spec_close_preserves_others
  sorry
-- !benchmark @end proof def=disprove_close_preserves_others
