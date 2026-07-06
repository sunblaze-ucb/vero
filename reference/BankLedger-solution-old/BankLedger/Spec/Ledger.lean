-- ============================================================
-- BankLedger/Spec/Ledger.lean
-- Specifications for ledger-wide operations.
-- DO NOT MODIFY specification definitions or theorem signatures.
-- Prove the theorems by replacing sorry with a valid proof.
-- ============================================================

import BankLedger.Harness

-- ── Specifications ───────────────────────────────────────────

/-- Creating a zero-balance account does not change total assets. -/
def spec_total_create_invariant (impl : RepoImpl) : Prop :=
  ∀ (id : AccountId) (ledger : Ledger),
    impl.accountExists id ledger = false →
    impl.totalAssets (impl.createAccount id ledger) = impl.totalAssets ledger

/-- numAccounts equals the length of accountList. -/
def spec_num_matches_list (impl : RepoImpl) : Prop :=
  ∀ (ledger : Ledger),
    impl.numAccounts ledger = (impl.accountList ledger).length

-- ── Theorems ─────────────────────────────────────────────────

-- @review v1 [ ] thm_total_create_invariant — Spec/Ledger, theorem, proof: sorry
theorem thm_total_create_invariant : spec_total_create_invariant canonical := by
-- !benchmark @start proof def=thm_total_create_invariant
  intro id ledger h
  simp only [canonical, Bank.createAccount, Bank.totalAssets, Bank.accountExists] at h ⊢
  simp [h]
-- !benchmark @end proof def=thm_total_create_invariant

-- @review v1 [ ] thm_num_matches_list — Spec/Ledger, theorem, proof: sorry
theorem thm_num_matches_list : spec_num_matches_list canonical := by
-- !benchmark @start proof def=thm_num_matches_list
  intro ledger
  simp [canonical, Bank.numAccounts, Bank.accountList, List.length_map]
-- !benchmark @end proof def=thm_num_matches_list
