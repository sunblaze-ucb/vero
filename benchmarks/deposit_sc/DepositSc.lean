import DepositSc.Impl.Bits
import DepositSc.Impl.Tree
import DepositSc.Impl.Merkle
import DepositSc.Impl.Contract
import DepositSc.Bundle
import DepositSc.Harness
import DepositSc.Spec.Bits
import DepositSc.Spec.Tree
import DepositSc.Spec.Merkle
import DepositSc.Spec.Contract
import DepositSc.Test

/-!
# DepositSc

Root import hub for the Ethereum deposit-smart-contract benchmark.
Translated from
[deposit-sc-dafny](https://github.com/ConsenSys/deposit-sc-dafny)
(ConsenSys, Apache 2.0). See `manifest.json` for the structured
layout.

The active library imports the curation-stage artifacts: types + sigs
+ stubs (with curator reference impls inside the `code` markers),
the per-package bundle (`Bundle.lean`), the harness
(`RepoImpl` + `canonical` + `joint_unsat` macro), specs, and
conformance tests. `Proof/` is deliberately not part of this library
— per-mode proof files are materialized downstream of curation at
pre-agent-gen.
-/
