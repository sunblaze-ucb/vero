import BankLedger.Impl.Account

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# BankLedger.Impl.Transaction

Transaction operations: `deposit`, `withdraw`. Signatures and
implementations live together. Signatures are fixed vocabulary
(DO NOT MODIFY). Function bodies are the curator's reference
implementations; the pipeline replaces them with `sorry` inside the
`code` markers before presenting the benchmark to the LLM.
-/

namespace Bank

-- ── API signatures (DO NOT MODIFY) ───────────────────────────
abbrev DepositSig  := AccountId → Balance → Ledger → Option Ledger
abbrev WithdrawSig := AccountId → Balance → Ledger → Option Ledger

end Bank

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- !benchmark @start code_aux def=deposit
-- !benchmark @end code_aux def=deposit

-- !curation @review v1 [ ] deposit — Impl/Transaction, exec-fn (API), reference impl
def Bank.deposit : Bank.DepositSig :=
-- !benchmark @start code def=deposit
  fun id amount ledger =>
    if ledger.any (fun a => a.id == id) then
      some (ledger.map fun a => if a.id == id then ⟨a.id, a.balance + amount⟩ else a)
    else none
-- !benchmark @end code def=deposit

-- !benchmark @start code_aux def=withdraw
-- !benchmark @end code_aux def=withdraw

-- !curation @review v1 [ ] withdraw — Impl/Transaction, exec-fn (API), reference impl
def Bank.withdraw : Bank.WithdrawSig :=
-- !benchmark @start code def=withdraw
  fun id amount ledger =>
    match ledger.find? (fun a => a.id == id) with
    | none => none
    | some a =>
      if amount ≤ a.balance then
        some (ledger.map fun x => if x.id == id then ⟨x.id, x.balance - amount⟩ else x)
      else none
-- !benchmark @end code def=withdraw
