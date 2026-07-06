-- ============================================================
-- BankLedger/Impl/Transfer.lean — SOLUTION
-- ============================================================

import BankLedger.Impl.Transaction

def Bank.transfer : Bank.TransferSig :=
  fun src dst amount ledger => do
    let ledger' ← Bank.withdraw src amount ledger
    Bank.deposit dst amount ledger'
