import BankLedger.Harness
import BankLedger.Spec.Ledger

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# BankLedger.Proof_modecodeproof.Ledger (illustration — `codeproof` mode)

Per-module proof file for the code+proof evaluation mode. Deterministic
from `Spec/Ledger.lean`: per spec S, emit `prove_S` + `unsat_S` +
`sat_S`. LLM fills exactly one body per spec.

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

-- !benchmark @start proof_aux def=unsat_total_create_invariant
-- !benchmark @end proof_aux def=unsat_total_create_invariant

theorem unsat_total_create_invariant : ¬ ∃ impl : RepoImpl, spec_total_create_invariant impl := by
-- !benchmark @start proof def=unsat_total_create_invariant kind=unsat target=spec_total_create_invariant
  sorry
-- !benchmark @end proof def=unsat_total_create_invariant

-- !benchmark @start proof_aux def=sat_total_create_invariant
-- !benchmark @end proof_aux def=sat_total_create_invariant

theorem sat_total_create_invariant : ∃ impl : RepoImpl, spec_total_create_invariant impl := by
-- !benchmark @start proof def=sat_total_create_invariant kind=sat target=spec_total_create_invariant
  sorry
-- !benchmark @end proof def=sat_total_create_invariant

-- ── spec_num_matches_list ────────────────────────────────────

-- !benchmark @start proof_aux def=prove_num_matches_list
-- !benchmark @end proof_aux def=prove_num_matches_list

theorem prove_num_matches_list : spec_num_matches_list canonical := by
-- !benchmark @start proof def=prove_num_matches_list kind=prove target=spec_num_matches_list
  sorry
-- !benchmark @end proof def=prove_num_matches_list

-- !benchmark @start proof_aux def=unsat_num_matches_list
-- !benchmark @end proof_aux def=unsat_num_matches_list

theorem unsat_num_matches_list : ¬ ∃ impl : RepoImpl, spec_num_matches_list impl := by
-- !benchmark @start proof def=unsat_num_matches_list kind=unsat target=spec_num_matches_list
  sorry
-- !benchmark @end proof def=unsat_num_matches_list

-- !benchmark @start proof_aux def=sat_num_matches_list
-- !benchmark @end proof_aux def=sat_num_matches_list

theorem sat_num_matches_list : ∃ impl : RepoImpl, spec_num_matches_list impl := by
-- !benchmark @start proof def=sat_num_matches_list kind=sat target=spec_num_matches_list
  sorry
-- !benchmark @end proof def=sat_num_matches_list
