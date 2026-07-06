-- ============================================================
-- BankLedger/Types.lean
-- Core data types for the Bank Ledger benchmark.
-- DO NOT MODIFY any type definitions in this file.
-- ============================================================

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
