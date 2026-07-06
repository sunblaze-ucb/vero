-- ============================================================
-- BankLedger/Test.lean — SOLUTION
-- ============================================================

import BankLedger.Harness

#guard Bank.accountExists 1 [] == false
#guard Bank.accountExists 1 (Bank.createAccount 1 []) == true
#guard Bank.getBalance 1 (Bank.createAccount 1 []) == some 0
#guard Bank.accountExists 1 (Bank.closeAccount 1 (Bank.createAccount 1 [])) == false
#guard (do let l ← Bank.deposit 1 100 (Bank.createAccount 1 []); pure (Bank.getBalance 1 l)) == some (some 100)
#guard (do let l ← Bank.deposit 1 100 (Bank.createAccount 1 []); let l ← Bank.withdraw 1 40 l; pure (Bank.getBalance 1 l)) == some (some 60)
#guard (Bank.withdraw 1 200 (Bank.createAccount 1 [])) == none
#guard Bank.totalAssets [] == 0
#guard Bank.totalAssets [⟨1, 100⟩, ⟨2, 200⟩] == 300
#guard Bank.numAccounts [⟨1, 0⟩, ⟨2, 0⟩] == 2
#guard (Bank.accountList [⟨1, 0⟩, ⟨2, 0⟩]) == [1, 2]
