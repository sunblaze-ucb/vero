import BankLedger.Harness
import BankLedger.Spec.Account

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# BankLedger.Proof_modecodeproof.Account (illustration — `codeproof` mode)

Per-module proof file for the code+proof evaluation mode. Deterministic
from `Spec/Account.lean`: for each `spec_*`, the curator emits three
theorem stubs:

- `prove_S : spec_S canonical`
- `unsat_S : ¬ ∃ impl : RepoImpl, spec_S impl`
- `sat_S   : ∃ impl : RepoImpl, spec_S impl`

LLM fills exactly one body per spec; the other two stay as `sorry`.
The `sat_S` case is paired with S listed in the `!solution` block in
`Proof_modecodeproof/Joint.lean`.

Illustrative file, not imported by the root hub. See
`Proof_modecodeproof/Joint.lean` for the joint-unsat slot.
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

-- !benchmark @start proof_aux def=unsat_create_zero_balance
-- !benchmark @end proof_aux def=unsat_create_zero_balance

theorem unsat_create_zero_balance : ¬ ∃ impl : RepoImpl, spec_create_zero_balance impl := by
-- !benchmark @start proof def=unsat_create_zero_balance kind=unsat target=spec_create_zero_balance
  sorry
-- !benchmark @end proof def=unsat_create_zero_balance

-- !benchmark @start proof_aux def=sat_create_zero_balance
-- !benchmark @end proof_aux def=sat_create_zero_balance

theorem sat_create_zero_balance : ∃ impl : RepoImpl, spec_create_zero_balance impl := by
-- !benchmark @start proof def=sat_create_zero_balance kind=sat target=spec_create_zero_balance
  sorry
-- !benchmark @end proof def=sat_create_zero_balance

-- ── spec_create_exists ───────────────────────────────────────

-- !benchmark @start proof_aux def=prove_create_exists
-- !benchmark @end proof_aux def=prove_create_exists

theorem prove_create_exists : spec_create_exists canonical := by
-- !benchmark @start proof def=prove_create_exists kind=prove target=spec_create_exists
  sorry
-- !benchmark @end proof def=prove_create_exists

-- !benchmark @start proof_aux def=unsat_create_exists
-- !benchmark @end proof_aux def=unsat_create_exists

theorem unsat_create_exists : ¬ ∃ impl : RepoImpl, spec_create_exists impl := by
-- !benchmark @start proof def=unsat_create_exists kind=unsat target=spec_create_exists
  sorry
-- !benchmark @end proof def=unsat_create_exists

-- !benchmark @start proof_aux def=sat_create_exists
-- !benchmark @end proof_aux def=sat_create_exists

theorem sat_create_exists : ∃ impl : RepoImpl, spec_create_exists impl := by
-- !benchmark @start proof def=sat_create_exists kind=sat target=spec_create_exists
  sorry
-- !benchmark @end proof def=sat_create_exists

-- ── spec_close_removes ───────────────────────────────────────

-- !benchmark @start proof_aux def=prove_close_removes
-- !benchmark @end proof_aux def=prove_close_removes

theorem prove_close_removes : spec_close_removes canonical := by
-- !benchmark @start proof def=prove_close_removes kind=prove target=spec_close_removes
  sorry
-- !benchmark @end proof def=prove_close_removes

-- !benchmark @start proof_aux def=unsat_close_removes
-- !benchmark @end proof_aux def=unsat_close_removes

theorem unsat_close_removes : ¬ ∃ impl : RepoImpl, spec_close_removes impl := by
-- !benchmark @start proof def=unsat_close_removes kind=unsat target=spec_close_removes
  sorry
-- !benchmark @end proof def=unsat_close_removes

-- !benchmark @start proof_aux def=sat_close_removes
-- !benchmark @end proof_aux def=sat_close_removes

theorem sat_close_removes : ∃ impl : RepoImpl, spec_close_removes impl := by
-- !benchmark @start proof def=sat_close_removes kind=sat target=spec_close_removes
  sorry
-- !benchmark @end proof def=sat_close_removes

-- ── spec_close_preserves_others ──────────────────────────────

-- !benchmark @start proof_aux def=prove_close_preserves_others
-- !benchmark @end proof_aux def=prove_close_preserves_others

theorem prove_close_preserves_others : spec_close_preserves_others canonical := by
-- !benchmark @start proof def=prove_close_preserves_others kind=prove target=spec_close_preserves_others
  sorry
-- !benchmark @end proof def=prove_close_preserves_others

-- !benchmark @start proof_aux def=unsat_close_preserves_others
-- !benchmark @end proof_aux def=unsat_close_preserves_others

theorem unsat_close_preserves_others : ¬ ∃ impl : RepoImpl, spec_close_preserves_others impl := by
-- !benchmark @start proof def=unsat_close_preserves_others kind=unsat target=spec_close_preserves_others
  sorry
-- !benchmark @end proof def=unsat_close_preserves_others

-- !benchmark @start proof_aux def=sat_close_preserves_others
-- !benchmark @end proof_aux def=sat_close_preserves_others

theorem sat_close_preserves_others : ∃ impl : RepoImpl, spec_close_preserves_others impl := by
-- !benchmark @start proof def=sat_close_preserves_others kind=sat target=spec_close_preserves_others
  sorry
-- !benchmark @end proof def=sat_close_preserves_others
