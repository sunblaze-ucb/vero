-- !benchmark @start imports
-- !benchmark @end imports

/-!
# BankLedger.Impl.Account

Core data types, signatures, and implementations for account management.
Types and signatures are fixed vocabulary (DO NOT MODIFY). Function
bodies are the curator's reference implementations; the pipeline
replaces them with `sorry` inside the `code` markers before presenting
the benchmark to the LLM.
-/

-- ── Core data types (DO NOT MODIFY) ──────────────────────────

/-- Unique identifier for a bank account. -/
abbrev AccountId := Nat

/-- Non-negative monetary amount. -/
abbrev Balance := Nat

/-- A single bank account with an ID and a balance. -/
structure Account where
  id : AccountId
  balance : Balance
  deriving Repr, DecidableEq, BEq

/-- A ledger is an ordered list of accounts. No duplicate IDs by convention. -/
abbrev Ledger := List Account

namespace Bank

-- ── API signatures (DO NOT MODIFY) ───────────────────────────
abbrev CreateAccountSig  := AccountId → Ledger → Ledger
abbrev CloseAccountSig   := AccountId → Ledger → Ledger
abbrev AccountExistsSig  := AccountId → Ledger → Bool
abbrev GetBalanceSig     := AccountId → Ledger → Option Balance

end Bank

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- !benchmark @start code_aux def=createAccount
-- !benchmark @end code_aux def=createAccount

-- !curation @review v1 [ ] createAccount — Impl/Account, exec-fn (API), reference impl
def Bank.createAccount : Bank.CreateAccountSig :=
-- !benchmark @start code def=createAccount
  fun id ledger =>
    if ledger.any (fun a => a.id == id) then ledger
    else ⟨id, 0⟩ :: ledger
-- !benchmark @end code def=createAccount

-- !benchmark @start code_aux def=closeAccount
-- !benchmark @end code_aux def=closeAccount

-- !curation @review v1 [ ] closeAccount — Impl/Account, exec-fn (API), reference impl
def Bank.closeAccount : Bank.CloseAccountSig :=
-- !benchmark @start code def=closeAccount
  fun id ledger =>
    ledger.filter (fun a => !(a.id == id))
-- !benchmark @end code def=closeAccount

-- !benchmark @start code_aux def=accountExists
-- !benchmark @end code_aux def=accountExists

-- !curation @review v1 [ ] accountExists — Impl/Account, exec-fn (API), reference impl
def Bank.accountExists : Bank.AccountExistsSig :=
-- !benchmark @start code def=accountExists
  fun id ledger =>
    ledger.any (fun a => a.id == id)
-- !benchmark @end code def=accountExists

-- !benchmark @start code_aux def=getBalance
-- !benchmark @end code_aux def=getBalance

-- !curation @review v1 [ ] getBalance — Impl/Account, exec-fn (API), reference impl
def Bank.getBalance : Bank.GetBalanceSig :=
-- !benchmark @start code def=getBalance
  fun id ledger =>
    (ledger.find? (fun a => a.id == id)).map Account.balance
-- !benchmark @end code def=getBalance
