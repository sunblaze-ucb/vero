import BankLedger.Harness
import BankLedger.Spec.Transfer

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# BankLedger.Proof_modeproof.Transfer (illustration — `proof` mode)

Per-module proof file for the proof-only evaluation mode. Deterministic
from `Spec/Transfer.lean`: per spec S, emit `prove_S` + `disprove_S`.
LLM fills exactly one of each pair; the other stays as `sorry`.

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

-- !benchmark @start proof_aux def=disprove_transfer_preserves_total
-- !benchmark @end proof_aux def=disprove_transfer_preserves_total

theorem disprove_transfer_preserves_total : ¬ spec_transfer_preserves_total canonical := by
-- !benchmark @start proof def=disprove_transfer_preserves_total kind=disprove target=spec_transfer_preserves_total
  sorry
-- !benchmark @end proof def=disprove_transfer_preserves_total

-- ── spec_transfer_updates_both ───────────────────────────────

-- !benchmark @start proof_aux def=prove_transfer_updates_both
-- !benchmark @end proof_aux def=prove_transfer_updates_both

theorem prove_transfer_updates_both : spec_transfer_updates_both canonical := by
-- !benchmark @start proof def=prove_transfer_updates_both kind=prove target=spec_transfer_updates_both
  sorry
-- !benchmark @end proof def=prove_transfer_updates_both

-- !benchmark @start proof_aux def=disprove_transfer_updates_both
-- !benchmark @end proof_aux def=disprove_transfer_updates_both

theorem disprove_transfer_updates_both : ¬ spec_transfer_updates_both canonical := by
-- !benchmark @start proof def=disprove_transfer_updates_both kind=disprove target=spec_transfer_updates_both
  sorry
-- !benchmark @end proof def=disprove_transfer_updates_both
