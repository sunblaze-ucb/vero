import BankLedger.Harness

/-!
# BankLedger.Spec.Transaction

Specifications for `deposit` and `withdraw`. Each `spec_*` is a
property over an arbitrary `impl : RepoImpl`; theorem stubs live
in `BankLedger/Proof/Transaction.lean`.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- Depositing into an existing account increases its balance by the exact amount. -/
def spec_deposit_increases (impl : RepoImpl) : Prop :=
  ∀ (id : AccountId) (amount : Balance) (ledger : Ledger) (bal : Balance),
    impl.bankLedger.getBalance id ledger = some bal →
    ∃ ledger', impl.bankLedger.deposit id amount ledger = some ledger' ∧
      impl.bankLedger.getBalance id ledger' = some (bal + amount)

/-- Withdrawing from an account with sufficient funds decreases balance by the exact amount. -/
def spec_withdraw_decreases (impl : RepoImpl) : Prop :=
  ∀ (id : AccountId) (amount : Balance) (ledger : Ledger) (bal : Balance),
    impl.bankLedger.getBalance id ledger = some bal →
    amount ≤ bal →
    ∃ ledger', impl.bankLedger.withdraw id amount ledger = some ledger' ∧
      impl.bankLedger.getBalance id ledger' = some (bal - amount)

/-- Withdrawing more than the balance fails (returns none). -/
def spec_withdraw_insufficient (impl : RepoImpl) : Prop :=
  ∀ (id : AccountId) (amount : Balance) (ledger : Ledger) (bal : Balance),
    impl.bankLedger.getBalance id ledger = some bal →
    amount > bal →
    impl.bankLedger.withdraw id amount ledger = none
