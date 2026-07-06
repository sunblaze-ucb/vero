-- ============================================================
-- BankLedger/Impl/Account.lean — SOLUTION
-- ============================================================

import BankLedger.Sig

def Bank.createAccount : Bank.CreateAccountSig :=
  fun id ledger =>
    if ledger.any (fun a => a.id == id) then ledger
    else ⟨id, 0⟩ :: ledger

def Bank.closeAccount : Bank.CloseAccountSig :=
  fun id ledger =>
    ledger.filter (fun a => decide (a.id ≠ id))

def Bank.accountExists : Bank.AccountExistsSig :=
  fun id ledger =>
    ledger.any (fun a => a.id == id)

def Bank.getBalance : Bank.GetBalanceSig :=
  fun id ledger =>
    (ledger.find? (fun a => a.id == id)).map Account.balance
