import BankLedger.Impl.Account
import BankLedger.Impl.Transaction
import BankLedger.Impl.Transfer
import BankLedger.Impl.Ledger

/-!
# BankLedger.Bundle

Per-package implementation bundle for the `BankLedger` root package.
Collects all 10 API signatures into one structure.

In `Harness.lean`, `RepoImpl` is an `abbrev` for this bundle
(single-package benchmark — flat shape via transparent alias).
Multi-package benchmarks would have a sibling `Bundle.lean` per
package, wired into a nested `structure RepoImpl` in `Harness.lean`.

DO NOT MODIFY — benchmark infrastructure.
-/

structure BankLedgerBundle where
  createAccount  : Bank.CreateAccountSig
  closeAccount   : Bank.CloseAccountSig
  accountExists  : Bank.AccountExistsSig
  getBalance     : Bank.GetBalanceSig
  deposit        : Bank.DepositSig
  withdraw       : Bank.WithdrawSig
  transfer       : Bank.TransferSig
  totalAssets    : Bank.TotalAssetsSig
  accountList    : Bank.AccountListSig
  numAccounts    : Bank.NumAccountsSig
