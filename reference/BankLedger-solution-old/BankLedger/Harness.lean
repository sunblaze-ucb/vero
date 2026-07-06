-- ============================================================
-- BankLedger/Harness.lean
-- Benchmark harness: implementation bundle, canonical instance,
-- and the unsat_check macro for satisfiability analysis.
-- DO NOT MODIFY this file. This is the benchmark infrastructure.
-- ============================================================

import BankLedger.Impl.Account
import BankLedger.Impl.Transaction
import BankLedger.Impl.Transfer
import BankLedger.Impl.Ledger

-- ── Implementation bundle ────────────────────────────────────
-- All API signatures collected into a single structure.
-- Specifications are parameterized by this structure so they
-- can quantify over arbitrary implementations.

structure RepoImpl where
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

-- ── Canonical instance ───────────────────────────────────────
-- Instantiates the bundle with the implementations from Impl/.

def canonical : RepoImpl where
  createAccount  := Bank.createAccount
  closeAccount   := Bank.closeAccount
  accountExists  := Bank.accountExists
  getBalance     := Bank.getBalance
  deposit        := Bank.deposit
  withdraw       := Bank.withdraw
  transfer       := Bank.transfer
  totalAssets    := Bank.totalAssets
  accountList    := Bank.accountList
  numAccounts    := Bank.numAccounts

-- ── Unsatisfiability macro ───────────────────────────────────
-- Use `unsat_check` to generate a theorem stating that the given
-- specifications are jointly unsatisfiable for any `RepoImpl`.
-- The LLM provides the proof after `by`.
--
-- Usage:
--   unsat_check spec_foo spec_bar by
--     intro ⟨impl, h1, h2⟩
--     ...
--
-- Expands to:
--   theorem unsat.spec_foo.spec_bar :
--     ¬ ∃ impl : RepoImpl, spec_foo impl ∧ spec_bar impl := by
--     intro ⟨impl, h1, h2⟩
--     ...

syntax "unsat_check" ident ident ident* "by" tacticSeq : command

open Lean in
macro_rules
  | `(unsat_check $s1 $s2 $[$rest]* by $proof) => do
    let specs := #[s1, s2] ++ rest
    let name := specs.foldl (init := `unsat) fun acc s => Name.append acc s.getId
    let mut body ← `($s1 impl)
    for s in specs[1:] do
      body ← `($body ∧ $s impl)
    `(theorem $(mkIdent name) : ¬ ∃ impl : RepoImpl, $body := by $proof)
