-- ============================================================
-- BankLedger/Spec/Transfer.lean
-- Specifications for the transfer operation.
-- DO NOT MODIFY specification definitions or theorem signatures.
-- Prove the theorems by replacing sorry with a valid proof.
-- ============================================================

import BankLedger.Harness

-- ── Specifications ───────────────────────────────────────────

/-- A successful transfer preserves the total assets across the ledger. -/
def spec_transfer_preserves_total (impl : RepoImpl) : Prop :=
  ∀ (src dst : AccountId) (amount : Balance) (ledger ledger' : Ledger),
    impl.transfer src dst amount ledger = some ledger' →
    impl.totalAssets ledger' = impl.totalAssets ledger

/-- A successful transfer between distinct accounts updates both balances correctly. -/
def spec_transfer_updates_both (impl : RepoImpl) : Prop :=
  ∀ (src dst : AccountId) (amount : Balance) (ledger ledger' : Ledger)
    (srcBal dstBal : Balance),
    src ≠ dst →
    impl.getBalance src ledger = some srcBal →
    impl.getBalance dst ledger = some dstBal →
    amount ≤ srcBal →
    impl.transfer src dst amount ledger = some ledger' →
    impl.getBalance src ledger' = some (srcBal - amount) ∧
    impl.getBalance dst ledger' = some (dstBal + amount)

-- ── Theorems ─────────────────────────────────────────────────

-- @review v1 [ ] thm_transfer_preserves_total — Spec/Transfer, theorem, proof: sorry
theorem thm_transfer_preserves_total : spec_transfer_preserves_total canonical := by
-- !benchmark @start proof def=thm_transfer_preserves_total
  sorry
-- !benchmark @end proof def=thm_transfer_preserves_total

-- @review v1 [ ] thm_transfer_updates_both — Spec/Transfer, theorem, proof: sorry
theorem thm_transfer_updates_both : spec_transfer_updates_both canonical := by
-- !benchmark @start proof def=thm_transfer_updates_both
  sorry
-- !benchmark @end proof def=thm_transfer_updates_both
