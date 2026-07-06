import BankLedger.Impl.Account

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# BankLedger.Impl.Ledger

Ledger-wide operations: `totalAssets`, `accountList`, `numAccounts`.
Signatures and implementations live together. Signatures are fixed
vocabulary (DO NOT MODIFY). Function bodies are the curator's
reference implementations; the pipeline replaces them with `sorry`
inside the `code` markers before presenting the benchmark to the LLM.
-/

namespace Bank

-- ── API signatures (DO NOT MODIFY) ───────────────────────────
abbrev TotalAssetsSig := Ledger → Balance
abbrev AccountListSig := Ledger → List AccountId
abbrev NumAccountsSig := Ledger → Nat

end Bank

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- !benchmark @start code_aux def=totalAssets
-- !benchmark @end code_aux def=totalAssets

-- !curation @review v1 [ ] totalAssets — Impl/Ledger, exec-fn (API), reference impl
def Bank.totalAssets : Bank.TotalAssetsSig :=
-- !benchmark @start code def=totalAssets
  fun ledger =>
    ledger.foldl (fun acc a => acc + a.balance) 0
-- !benchmark @end code def=totalAssets

-- !benchmark @start code_aux def=accountList
-- !benchmark @end code_aux def=accountList

-- !curation @review v1 [ ] accountList — Impl/Ledger, exec-fn (API), reference impl
def Bank.accountList : Bank.AccountListSig :=
-- !benchmark @start code def=accountList
  fun ledger =>
    ledger.map (fun a => a.id)
-- !benchmark @end code def=accountList

-- !benchmark @start code_aux def=numAccounts
-- !benchmark @end code_aux def=numAccounts

-- !curation @review v1 [ ] numAccounts — Impl/Ledger, exec-fn (API), reference impl
def Bank.numAccounts : Bank.NumAccountsSig :=
-- !benchmark @start code def=numAccounts
  fun ledger =>
    ledger.length
-- !benchmark @end code def=numAccounts
