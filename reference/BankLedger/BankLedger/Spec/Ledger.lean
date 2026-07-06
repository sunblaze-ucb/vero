import BankLedger.Harness

/-!
# BankLedger.Spec.Ledger

Specifications for ledger-wide operations. Each `spec_*` is a
property over an arbitrary `impl : RepoImpl`; theorem stubs live
in `BankLedger/Proof/Ledger.lean`.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- Creating a zero-balance account does not change total assets. -/
def spec_total_create_invariant (impl : RepoImpl) : Prop :=
  ∀ (id : AccountId) (ledger : Ledger),
    impl.bankLedger.accountExists id ledger = false →
    impl.bankLedger.totalAssets (impl.bankLedger.createAccount id ledger) =
      impl.bankLedger.totalAssets ledger

/-- numAccounts equals the length of accountList. -/
def spec_num_matches_list (impl : RepoImpl) : Prop :=
  ∀ (ledger : Ledger),
    impl.bankLedger.numAccounts ledger = (impl.bankLedger.accountList ledger).length
