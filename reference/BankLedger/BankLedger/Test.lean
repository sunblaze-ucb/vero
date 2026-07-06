import BankLedger.Impl.Account
import BankLedger.Impl.Transaction
import BankLedger.Impl.Transfer
import BankLedger.Impl.Ledger

/-!
# BankLedger.Test

Executable conformance tests. `#guard` assertions run against the
curator's reference implementations that live INSIDE the `code`
markers in `Impl/*.lean`. Before the LLM sees the benchmark, the
pipeline replaces marker contents with `sorry` — these guards catch
regressions in the reference impls themselves, not in LLM submissions.

DO NOT MODIFY — infrastructure.
-/

open Bank

-- ── accountExists / createAccount / getBalance ─────────────────
#guard accountExists 1 [] == false
#guard accountExists 1 (createAccount 1 []) == true
#guard getBalance 1 (createAccount 1 []) == some 0

-- ── closeAccount ───────────────────────────────────────────────
#guard accountExists 1 (closeAccount 1 (createAccount 1 [])) == false

-- ── deposit / withdraw ─────────────────────────────────────────
#guard (deposit 1 100 (createAccount 1 []) >>= getBalance 1) == some 100
#guard (do
    let l1 ← deposit 1 100 (createAccount 1 [])
    let l2 ← withdraw 1 40 l1
    getBalance 1 l2) == some 60
#guard withdraw 1 200 (createAccount 1 []) == none

-- ── totalAssets / numAccounts / accountList ────────────────────
#guard totalAssets [] == 0
#guard totalAssets [⟨1, 100⟩, ⟨2, 200⟩] == 300
#guard numAccounts [⟨1, 0⟩, ⟨2, 0⟩] == 2
#guard accountList [⟨1, 0⟩, ⟨2, 0⟩] == [1, 2]

-- ── transfer preserves total, moves funds ──────────────────────
#guard (transfer 1 2 30 [⟨1, 100⟩, ⟨2, 50⟩]).map totalAssets == some 150
#guard (transfer 1 2 30 [⟨1, 100⟩, ⟨2, 50⟩]) >>= getBalance 1 == some 70
#guard (transfer 1 2 30 [⟨1, 100⟩, ⟨2, 50⟩]) >>= getBalance 2 == some 80
#guard transfer 1 2 200 [⟨1, 100⟩, ⟨2, 50⟩] == none
