-- ============================================================
-- BankLedger/Spec/Account.lean
-- Specifications for account management operations.
-- DO NOT MODIFY specification definitions or theorem signatures.
-- Prove the theorems by replacing sorry with a valid proof.
-- ============================================================

import BankLedger.Harness

-- ── Specifications ───────────────────────────────────────────

/-- Creating a new account gives it zero balance. -/
def spec_create_zero_balance (impl : RepoImpl) : Prop :=
  ∀ (id : AccountId) (ledger : Ledger),
    impl.accountExists id ledger = false →
    impl.getBalance id (impl.createAccount id ledger) = some 0

/-- After creating an account, it exists in the ledger. -/
def spec_create_exists (impl : RepoImpl) : Prop :=
  ∀ (id : AccountId) (ledger : Ledger),
    impl.accountExists id (impl.createAccount id ledger) = true

/-- Closing an account removes it from the ledger. -/
def spec_close_removes (impl : RepoImpl) : Prop :=
  ∀ (id : AccountId) (ledger : Ledger),
    impl.accountExists id (impl.closeAccount id ledger) = false

/-- Closing one account does not affect other accounts' balances. -/
def spec_close_preserves_others (impl : RepoImpl) : Prop :=
  ∀ (id other : AccountId) (ledger : Ledger),
    id ≠ other →
    impl.getBalance other (impl.closeAccount id ledger) =
    impl.getBalance other ledger

-- ── Theorems ─────────────────────────────────────────────────

-- @review v1 [ ] thm_create_zero_balance — Spec/Account, theorem, proof: sorry
theorem thm_create_zero_balance : spec_create_zero_balance canonical := by
-- !benchmark @start proof def=thm_create_zero_balance
  intro id ledger h
  simp only [canonical, Bank.createAccount, Bank.accountExists] at *
  simp only [h]
  simp only [Bank.getBalance, BEq.beq]
  simp
-- !benchmark @end proof def=thm_create_zero_balance

-- @review v1 [ ] thm_create_exists — Spec/Account, theorem, proof: sorry
theorem thm_create_exists : spec_create_exists canonical := by
-- !benchmark @start proof def=thm_create_exists
  intro id ledger
  simp only [canonical, Bank.createAccount, Bank.accountExists]
  split
  · assumption
  · simp [List.any_cons, BEq.beq]
-- !benchmark @end proof def=thm_create_exists

-- @review v1 [ ] thm_close_removes — Spec/Account, theorem, proof: sorry
theorem thm_close_removes : spec_close_removes canonical := by
-- !benchmark @start proof def=thm_close_removes
  intro id ledger
  simp only [canonical, Bank.closeAccount, Bank.accountExists]
  induction ledger with
  | nil => simp
  | cons a tl ih =>
    simp only [List.filter_cons, BEq.beq]
    split <;> simp_all
-- !benchmark @end proof def=thm_close_removes

-- @review v1 [ ] thm_close_preserves_others — Spec/Account, theorem, proof: sorry
theorem thm_close_preserves_others : spec_close_preserves_others canonical := by
-- !benchmark @start proof def=thm_close_preserves_others
  intro id other ledger hne
  simp only [canonical, Bank.closeAccount, Bank.getBalance]
  induction ledger with
  | nil => simp
  | cons a tl ih =>
    simp only [List.filter_cons, BEq.beq]
    by_cases haid : decide (a.id ≠ id) = true
    · -- a passes the filter (a.id ≠ id)
      simp only [haid, ite_true, List.find?_cons]
      by_cases hother : decide (a.id = other) = true
      · simp [hother]
      · simp only [hother]; exact ih
    · -- a is filtered out (a.id = id)
      simp only [haid]
      have haid' : a.id = id := by simpa using haid
      have hneq : decide (a.id = other) = false := by
        simp only [decide_eq_false_iff_not]; rw [haid']; exact hne
      simp only [List.find?_cons, hneq]; exact ih
-- !benchmark @end proof def=thm_close_preserves_others
