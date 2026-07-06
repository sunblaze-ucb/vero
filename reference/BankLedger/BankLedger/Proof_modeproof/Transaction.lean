import BankLedger.Harness
import BankLedger.Spec.Transaction

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# BankLedger.Proof_modeproof.Transaction (illustration — `proof` mode)

Per-module proof file for the proof-only evaluation mode. Deterministic
from `Spec/Transaction.lean`: per spec S, emit `prove_S` + `disprove_S`.
LLM fills exactly one of each pair; the other stays as `sorry`.

Illustrative file, not imported by the root hub.
-/

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- ── spec_deposit_increases ───────────────────────────────────

-- !benchmark @start proof_aux def=prove_deposit_increases
-- !benchmark @end proof_aux def=prove_deposit_increases

theorem prove_deposit_increases : spec_deposit_increases canonical := by
-- !benchmark @start proof def=prove_deposit_increases kind=prove target=spec_deposit_increases
  sorry
-- !benchmark @end proof def=prove_deposit_increases

-- !benchmark @start proof_aux def=disprove_deposit_increases
-- !benchmark @end proof_aux def=disprove_deposit_increases

theorem disprove_deposit_increases : ¬ spec_deposit_increases canonical := by
-- !benchmark @start proof def=disprove_deposit_increases kind=disprove target=spec_deposit_increases
  sorry
-- !benchmark @end proof def=disprove_deposit_increases

-- ── spec_withdraw_decreases ──────────────────────────────────

-- !benchmark @start proof_aux def=prove_withdraw_decreases
-- !benchmark @end proof_aux def=prove_withdraw_decreases

theorem prove_withdraw_decreases : spec_withdraw_decreases canonical := by
-- !benchmark @start proof def=prove_withdraw_decreases kind=prove target=spec_withdraw_decreases
  sorry
-- !benchmark @end proof def=prove_withdraw_decreases

-- !benchmark @start proof_aux def=disprove_withdraw_decreases
-- !benchmark @end proof_aux def=disprove_withdraw_decreases

theorem disprove_withdraw_decreases : ¬ spec_withdraw_decreases canonical := by
-- !benchmark @start proof def=disprove_withdraw_decreases kind=disprove target=spec_withdraw_decreases
  sorry
-- !benchmark @end proof def=disprove_withdraw_decreases

-- ── spec_withdraw_insufficient ───────────────────────────────

-- !benchmark @start proof_aux def=prove_withdraw_insufficient
-- !benchmark @end proof_aux def=prove_withdraw_insufficient

theorem prove_withdraw_insufficient : spec_withdraw_insufficient canonical := by
-- !benchmark @start proof def=prove_withdraw_insufficient kind=prove target=spec_withdraw_insufficient
  sorry
-- !benchmark @end proof def=prove_withdraw_insufficient

-- !benchmark @start proof_aux def=disprove_withdraw_insufficient
-- !benchmark @end proof_aux def=disprove_withdraw_insufficient

theorem disprove_withdraw_insufficient : ¬ spec_withdraw_insufficient canonical := by
-- !benchmark @start proof def=disprove_withdraw_insufficient kind=disprove target=spec_withdraw_insufficient
  sorry
-- !benchmark @end proof def=disprove_withdraw_insufficient
