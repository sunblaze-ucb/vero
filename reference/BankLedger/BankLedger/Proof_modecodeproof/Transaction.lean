import BankLedger.Harness
import BankLedger.Spec.Transaction

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# BankLedger.Proof_modecodeproof.Transaction (illustration — `codeproof` mode)

Per-module proof file for the code+proof evaluation mode. Deterministic
from `Spec/Transaction.lean`: per spec S, emit `prove_S` + `unsat_S` +
`sat_S`. LLM fills exactly one body per spec.

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

-- !benchmark @start proof_aux def=unsat_deposit_increases
-- !benchmark @end proof_aux def=unsat_deposit_increases

theorem unsat_deposit_increases : ¬ ∃ impl : RepoImpl, spec_deposit_increases impl := by
-- !benchmark @start proof def=unsat_deposit_increases kind=unsat target=spec_deposit_increases
  sorry
-- !benchmark @end proof def=unsat_deposit_increases

-- !benchmark @start proof_aux def=sat_deposit_increases
-- !benchmark @end proof_aux def=sat_deposit_increases

theorem sat_deposit_increases : ∃ impl : RepoImpl, spec_deposit_increases impl := by
-- !benchmark @start proof def=sat_deposit_increases kind=sat target=spec_deposit_increases
  sorry
-- !benchmark @end proof def=sat_deposit_increases

-- ── spec_withdraw_decreases ──────────────────────────────────

-- !benchmark @start proof_aux def=prove_withdraw_decreases
-- !benchmark @end proof_aux def=prove_withdraw_decreases

theorem prove_withdraw_decreases : spec_withdraw_decreases canonical := by
-- !benchmark @start proof def=prove_withdraw_decreases kind=prove target=spec_withdraw_decreases
  sorry
-- !benchmark @end proof def=prove_withdraw_decreases

-- !benchmark @start proof_aux def=unsat_withdraw_decreases
-- !benchmark @end proof_aux def=unsat_withdraw_decreases

theorem unsat_withdraw_decreases : ¬ ∃ impl : RepoImpl, spec_withdraw_decreases impl := by
-- !benchmark @start proof def=unsat_withdraw_decreases kind=unsat target=spec_withdraw_decreases
  sorry
-- !benchmark @end proof def=unsat_withdraw_decreases

-- !benchmark @start proof_aux def=sat_withdraw_decreases
-- !benchmark @end proof_aux def=sat_withdraw_decreases

theorem sat_withdraw_decreases : ∃ impl : RepoImpl, spec_withdraw_decreases impl := by
-- !benchmark @start proof def=sat_withdraw_decreases kind=sat target=spec_withdraw_decreases
  sorry
-- !benchmark @end proof def=sat_withdraw_decreases

-- ── spec_withdraw_insufficient ───────────────────────────────

-- !benchmark @start proof_aux def=prove_withdraw_insufficient
-- !benchmark @end proof_aux def=prove_withdraw_insufficient

theorem prove_withdraw_insufficient : spec_withdraw_insufficient canonical := by
-- !benchmark @start proof def=prove_withdraw_insufficient kind=prove target=spec_withdraw_insufficient
  sorry
-- !benchmark @end proof def=prove_withdraw_insufficient

-- !benchmark @start proof_aux def=unsat_withdraw_insufficient
-- !benchmark @end proof_aux def=unsat_withdraw_insufficient

theorem unsat_withdraw_insufficient : ¬ ∃ impl : RepoImpl, spec_withdraw_insufficient impl := by
-- !benchmark @start proof def=unsat_withdraw_insufficient kind=unsat target=spec_withdraw_insufficient
  sorry
-- !benchmark @end proof def=unsat_withdraw_insufficient

-- !benchmark @start proof_aux def=sat_withdraw_insufficient
-- !benchmark @end proof_aux def=sat_withdraw_insufficient

theorem sat_withdraw_insufficient : ∃ impl : RepoImpl, spec_withdraw_insufficient impl := by
-- !benchmark @start proof def=sat_withdraw_insufficient kind=sat target=spec_withdraw_insufficient
  sorry
-- !benchmark @end proof def=sat_withdraw_insufficient
