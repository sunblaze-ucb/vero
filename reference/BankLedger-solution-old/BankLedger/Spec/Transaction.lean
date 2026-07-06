-- ============================================================
-- BankLedger/Spec/Transaction.lean
-- Specifications for deposit and withdraw operations.
-- DO NOT MODIFY specification definitions or theorem signatures.
-- Prove the theorems by replacing sorry with a valid proof.
-- ============================================================

import BankLedger.Harness

-- ── Specifications ───────────────────────────────────────────

/-- Depositing into an existing account increases its balance by the exact amount. -/
def spec_deposit_increases (impl : RepoImpl) : Prop :=
  ∀ (id : AccountId) (amount : Balance) (ledger : Ledger) (bal : Balance),
    impl.getBalance id ledger = some bal →
    ∃ ledger', impl.deposit id amount ledger = some ledger' ∧
      impl.getBalance id ledger' = some (bal + amount)

/-- Withdrawing from an account with sufficient funds decreases balance by the exact amount. -/
def spec_withdraw_decreases (impl : RepoImpl) : Prop :=
  ∀ (id : AccountId) (amount : Balance) (ledger : Ledger) (bal : Balance),
    impl.getBalance id ledger = some bal →
    amount ≤ bal →
    ∃ ledger', impl.withdraw id amount ledger = some ledger' ∧
      impl.getBalance id ledger' = some (bal - amount)

/-- Withdrawing more than the balance fails (returns none). -/
def spec_withdraw_insufficient (impl : RepoImpl) : Prop :=
  ∀ (id : AccountId) (amount : Balance) (ledger : Ledger) (bal : Balance),
    impl.getBalance id ledger = some bal →
    amount > bal →
    impl.withdraw id amount ledger = none

-- ── Theorems ─────────────────────────────────────────────────

-- @review v1 [ ] thm_deposit_increases — Spec/Transaction, theorem, proof: sorry
theorem thm_deposit_increases : spec_deposit_increases canonical := by
-- !benchmark @start proof def=thm_deposit_increases
  sorry
-- !benchmark @end proof def=thm_deposit_increases

-- @review v1 [ ] thm_withdraw_decreases — Spec/Transaction, theorem, proof: sorry
theorem thm_withdraw_decreases : spec_withdraw_decreases canonical := by
-- !benchmark @start proof def=thm_withdraw_decreases
  sorry
-- !benchmark @end proof def=thm_withdraw_decreases

-- @review v1 [ ] thm_withdraw_insufficient — Spec/Transaction, theorem, proof: sorry
theorem thm_withdraw_insufficient : spec_withdraw_insufficient canonical := by
-- !benchmark @start proof def=thm_withdraw_insufficient
  sorry
-- !benchmark @end proof def=thm_withdraw_insufficient
