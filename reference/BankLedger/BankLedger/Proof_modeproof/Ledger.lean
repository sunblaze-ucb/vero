import BankLedger.Harness
import BankLedger.Spec.Ledger

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# BankLedger.Proof_modeproof.Ledger (illustration — `proof` mode)

Per-module proof file for the proof-only evaluation mode. Deterministic
from `Spec/Ledger.lean`: per spec S, emit `prove_S` + `disprove_S`.
LLM fills exactly one of each pair; the other stays as `sorry`.

Illustrative file, not imported by the root hub.
-/

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- ── spec_total_create_invariant ──────────────────────────────

-- !benchmark @start proof_aux def=prove_total_create_invariant
-- !benchmark @end proof_aux def=prove_total_create_invariant

theorem prove_total_create_invariant : spec_total_create_invariant canonical := by
-- !benchmark @start proof def=prove_total_create_invariant kind=prove target=spec_total_create_invariant
  sorry
-- !benchmark @end proof def=prove_total_create_invariant

-- !benchmark @start proof_aux def=disprove_total_create_invariant
-- !benchmark @end proof_aux def=disprove_total_create_invariant

theorem disprove_total_create_invariant : ¬ spec_total_create_invariant canonical := by
-- !benchmark @start proof def=disprove_total_create_invariant kind=disprove target=spec_total_create_invariant
  sorry
-- !benchmark @end proof def=disprove_total_create_invariant

-- ── spec_num_matches_list ────────────────────────────────────

-- !benchmark @start proof_aux def=prove_num_matches_list
-- !benchmark @end proof_aux def=prove_num_matches_list

theorem prove_num_matches_list : spec_num_matches_list canonical := by
-- !benchmark @start proof def=prove_num_matches_list kind=prove target=spec_num_matches_list
  sorry
-- !benchmark @end proof def=prove_num_matches_list

-- !benchmark @start proof_aux def=disprove_num_matches_list
-- !benchmark @end proof_aux def=disprove_num_matches_list

theorem disprove_num_matches_list : ¬ spec_num_matches_list canonical := by
-- !benchmark @start proof def=disprove_num_matches_list kind=disprove target=spec_num_matches_list
  sorry
-- !benchmark @end proof def=disprove_num_matches_list
