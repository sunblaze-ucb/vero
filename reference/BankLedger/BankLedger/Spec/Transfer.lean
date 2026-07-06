import BankLedger.Harness

/-!
# BankLedger.Spec.Transfer

Specifications for the `transfer` operation. Each `spec_*` is a
property over an arbitrary `impl : RepoImpl`; theorem stubs live
in `BankLedger/Proof/Transfer.lean`.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- A successful transfer preserves the total assets across the ledger. -/
def spec_transfer_preserves_total (impl : RepoImpl) : Prop :=
  ∀ (src dst : AccountId) (amount : Balance) (ledger ledger' : Ledger),
    impl.bankLedger.transfer src dst amount ledger = some ledger' →
    impl.bankLedger.totalAssets ledger' = impl.bankLedger.totalAssets ledger

/-- A successful transfer between distinct accounts updates both balances correctly. -/
def spec_transfer_updates_both (impl : RepoImpl) : Prop :=
  ∀ (src dst : AccountId) (amount : Balance) (ledger ledger' : Ledger)
    (srcBal dstBal : Balance),
    src ≠ dst →
    impl.bankLedger.getBalance src ledger = some srcBal →
    impl.bankLedger.getBalance dst ledger = some dstBal →
    amount ≤ srcBal →
    impl.bankLedger.transfer src dst amount ledger = some ledger' →
    impl.bankLedger.getBalance src ledger' = some (srcBal - amount) ∧
    impl.bankLedger.getBalance dst ledger' = some (dstBal + amount)
