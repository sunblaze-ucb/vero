import BankLedger.Impl.Transaction

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# BankLedger.Impl.Transfer

Transfer operation: move funds between accounts. Signature and
implementation live together. Signature is fixed vocabulary
(DO NOT MODIFY). Function body is the curator's reference
implementation; the pipeline replaces it with `sorry` inside the
`code` marker before presenting the benchmark to the LLM.
-/

namespace Bank

-- ── API signature (DO NOT MODIFY) ────────────────────────────
abbrev TransferSig := AccountId → AccountId → Balance → Ledger → Option Ledger

end Bank

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- !benchmark @start code_aux def=transfer
-- !benchmark @end code_aux def=transfer

-- !curation @review v1 [ ] transfer — Impl/Transfer, exec-fn (API), reference impl
def Bank.transfer : Bank.TransferSig :=
-- !benchmark @start code def=transfer
  fun src dst amount ledger =>
    match Bank.withdraw src amount ledger with
    | none => none
    | some l' => Bank.deposit dst amount l'
-- !benchmark @end code def=transfer
