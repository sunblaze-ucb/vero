import BankLedger.Harness

/-!
# BankLedger.Spec.Account

Specifications for account management operations. Each `spec_*` is
a property over an arbitrary `impl : RepoImpl`; theorem stubs live
in `BankLedger/Proof/Account.lean`.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- Creating a new account gives it zero balance. -/
def spec_create_zero_balance (impl : RepoImpl) : Prop :=
  ∀ (id : AccountId) (ledger : Ledger),
    impl.bankLedger.accountExists id ledger = false →
    impl.bankLedger.getBalance id (impl.bankLedger.createAccount id ledger) = some 0

/-- After creating an account, it exists in the ledger. -/
def spec_create_exists (impl : RepoImpl) : Prop :=
  ∀ (id : AccountId) (ledger : Ledger),
    impl.bankLedger.accountExists id (impl.bankLedger.createAccount id ledger) = true

/-- Closing an account removes it from the ledger. -/
def spec_close_removes (impl : RepoImpl) : Prop :=
  ∀ (id : AccountId) (ledger : Ledger),
    impl.bankLedger.accountExists id (impl.bankLedger.closeAccount id ledger) = false

/-- Closing one account does not affect other accounts' balances. -/
def spec_close_preserves_others (impl : RepoImpl) : Prop :=
  ∀ (id other : AccountId) (ledger : Ledger),
    id ≠ other →
    impl.bankLedger.getBalance other (impl.bankLedger.closeAccount id ledger) =
    impl.bankLedger.getBalance other ledger
