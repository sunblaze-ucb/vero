import Verdict.Impl.Crypto
import Verdict.Impl.Asn1
import Verdict.Impl.Base64
import Verdict.Impl.Issue
import Verdict.Impl.Validator
import Verdict.Impl.PolicyCommon
import Verdict.Impl.PolicyChrome
import Verdict.Impl.PolicyFirefox
import Verdict.Impl.PolicyOpenSSL
import Verdict.Impl.PolicyStandard
import Verdict.Impl.Convert
import Verdict.Impl.Hex
import Verdict.Bundle
import Verdict.Harness
import Verdict.Spec.Base64
import Verdict.Spec.Issue
import Verdict.Spec.Validator
import Verdict.Spec.PolicyCommon
import Verdict.Spec.PolicyChrome
import Verdict.Spec.PolicyFirefox
import Verdict.Spec.PolicyOpenSSL
import Verdict.Spec.PolicyStandard
import Verdict.Spec.Convert
import Verdict.Spec.Parser
import Verdict.Test

/-!
# Verdict

Root import hub for the X.509-validator benchmark. Translated from
[verdict](https://github.com/secure-foundations/verdict) (Microsoft Research,
Verus). See `manifest.json` for the structured layout.

The active library imports the curation-stage artifacts: types + sigs
+ stubs (with curator reference impls inside the `code` markers), the
per-package bundle (`Bundle.lean`), the harness
(`RepoImpl` + `canonical` + `joint_unsat` macro), specs, and
conformance tests. Cryptographic primitives are modelled as `opaque`
declarations in `Impl/Crypto.lean` with minimal `axiom` properties —
these are NOT benchmark tasks; the LLM must not implement or prove
them. They are declared in `manifest.json::trusted_axioms` so the
evaluator does not flag them as axiom leaks.

`Proof/` is deliberately not part of this library — per-mode proof
files are materialized downstream of curation at pre-agent-gen.
-/
