import BankLedger.Harness
import BankLedger.Spec.Transfer

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# BankLedger.Proof_modecodeproof.Transfer (illustration — `codeproof` mode)

Per-module proof file for the code+proof evaluation mode. Deterministic
from `Spec/Transfer.lean`: per spec S, emit `prove_S` + `unsat_S` +
`sat_S`. LLM fills exactly one body per spec.

Illustrative file, not imported by the root hub.
-/

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- ── spec_transfer_preserves_total ────────────────────────────

-- !benchmark @start proof_aux def=prove_transfer_preserves_total
-- !benchmark @end proof_aux def=prove_transfer_preserves_total

theorem prove_transfer_preserves_total : spec_transfer_preserves_total canonical := by
-- !benchmark @start proof def=prove_transfer_preserves_total kind=prove target=spec_transfer_preserves_total
  sorry
-- !benchmark @end proof def=prove_transfer_preserves_total

-- !benchmark @start proof_aux def=unsat_transfer_preserves_total
-- !benchmark @end proof_aux def=unsat_transfer_preserves_total

theorem unsat_transfer_preserves_total : ¬ ∃ impl : RepoImpl, spec_transfer_preserves_total impl := by
-- !benchmark @start proof def=unsat_transfer_preserves_total kind=unsat target=spec_transfer_preserves_total
  sorry
-- !benchmark @end proof def=unsat_transfer_preserves_total

-- !benchmark @start proof_aux def=sat_transfer_preserves_total
-- !benchmark @end proof_aux def=sat_transfer_preserves_total

theorem sat_transfer_preserves_total : ∃ impl : RepoImpl, spec_transfer_preserves_total impl := by
-- !benchmark @start proof def=sat_transfer_preserves_total kind=sat target=spec_transfer_preserves_total
  sorry
-- !benchmark @end proof def=sat_transfer_preserves_total

-- ── spec_transfer_updates_both ───────────────────────────────

-- !benchmark @start proof_aux def=prove_transfer_updates_both
-- !benchmark @end proof_aux def=prove_transfer_updates_both

theorem prove_transfer_updates_both : spec_transfer_updates_both canonical := by
-- !benchmark @start proof def=prove_transfer_updates_both kind=prove target=spec_transfer_updates_both
  sorry
-- !benchmark @end proof def=prove_transfer_updates_both

-- !benchmark @start proof_aux def=unsat_transfer_updates_both
-- !benchmark @end proof_aux def=unsat_transfer_updates_both

theorem unsat_transfer_updates_both : ¬ ∃ impl : RepoImpl, spec_transfer_updates_both impl := by
-- !benchmark @start proof def=unsat_transfer_updates_both kind=unsat target=spec_transfer_updates_both
  sorry
-- !benchmark @end proof def=unsat_transfer_updates_both

-- !benchmark @start proof_aux def=sat_transfer_updates_both
-- !benchmark @end proof_aux def=sat_transfer_updates_both

theorem sat_transfer_updates_both : ∃ impl : RepoImpl, spec_transfer_updates_both impl := by
-- !benchmark @start proof def=sat_transfer_updates_both kind=sat target=spec_transfer_updates_both
  sorry
-- !benchmark @end proof def=sat_transfer_updates_both
