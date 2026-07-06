-- ============================================================
-- BankLedger/Impl/Transaction.lean — SOLUTION
-- ============================================================

import BankLedger.Impl.Account

/-- Update the balance of the first account matching `id`. -/
private def updateFirst (id : AccountId) (f : Balance → Balance) : Ledger → Ledger
  | [] => []
  | a :: rest =>
    if a.id == id then ⟨a.id, f a.balance⟩ :: rest
    else a :: updateFirst id f rest

def Bank.deposit : Bank.DepositSig :=
  fun id amount ledger =>
    if Bank.accountExists id ledger then
      some (updateFirst id (· + amount) ledger)
    else
      none

def Bank.withdraw : Bank.WithdrawSig :=
  fun id amount ledger =>
    match Bank.getBalance id ledger with
    | some bal =>
      if amount ≤ bal then
        some (updateFirst id (· - amount) ledger)
      else
        none
    | none => none
