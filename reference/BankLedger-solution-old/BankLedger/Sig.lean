-- ============================================================
-- BankLedger/Sig.lean
-- API signatures for all bank operations.
-- DO NOT MODIFY any signatures in this file.
-- ============================================================

import BankLedger.Types

namespace Bank

-- Account operations
abbrev CreateAccountSig  := AccountId → Ledger → Ledger
abbrev CloseAccountSig   := AccountId → Ledger → Ledger
abbrev AccountExistsSig  := AccountId → Ledger → Bool
abbrev GetBalanceSig     := AccountId → Ledger → Option Balance

-- Transaction operations
abbrev DepositSig        := AccountId → Balance → Ledger → Option Ledger
abbrev WithdrawSig       := AccountId → Balance → Ledger → Option Ledger

-- Transfer operations
abbrev TransferSig       := AccountId → AccountId → Balance → Ledger → Option Ledger

-- Ledger-wide operations
abbrev TotalAssetsSig    := Ledger → Balance
abbrev AccountListSig    := Ledger → List AccountId
abbrev NumAccountsSig    := Ledger → Nat

end Bank
