import BankLedger.Impl.Account
import BankLedger.Impl.Transaction
import BankLedger.Impl.Transfer
import BankLedger.Impl.Ledger
import BankLedger.Bundle
import BankLedger.Harness
import BankLedger.Spec.Account
import BankLedger.Spec.Transaction
import BankLedger.Spec.Transfer
import BankLedger.Spec.Ledger
import BankLedger.Test

/-!
# BankLedger

Root import hub for the BankLedger reference benchmark. See
`reference/README.md` for the paradigm and how the pieces fit together.

The active library imports the curation-stage artifacts: types, sigs,
stubs, the per-package bundle (`Bundle.lean`), the harness (RepoImpl
alias + canonical + `joint_unsat` macro), specs, and conformance
tests. `Proof/` is deliberately NOT part of this library — per-mode
proof files are materialized downstream of curation (pre-agent-gen
stage). Two illustrative sidecars live alongside for reference:

- `BankLedger/Proof_modeproof/`     — `proof` mode (prove + disprove per spec)
- `BankLedger/Proof_modecodeproof/` — `codeproof` mode (prove + unsat + sat per spec, plus one joint slot)
-/
