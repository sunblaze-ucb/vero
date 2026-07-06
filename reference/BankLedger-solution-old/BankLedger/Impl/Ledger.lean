-- ============================================================
-- BankLedger/Impl/Ledger.lean — SOLUTION
-- ============================================================

import BankLedger.Impl.Account

def Bank.totalAssets : Bank.TotalAssetsSig :=
  fun ledger => ledger.foldl (fun acc a => acc + a.balance) 0

def Bank.accountList : Bank.AccountListSig :=
  fun ledger => ledger.map Account.id

def Bank.numAccounts : Bank.NumAccountsSig :=
  fun ledger => ledger.length
