import Verdict.Harness

/-!
# Verdict.Spec.PolicyChrome

Specifications for Chrome-specific policy APIs (`chromeCertVerifiedLeaf`,
`chromeCertVerifiedIntermediate`, `chromeCertVerifiedRoot`,
`chromeCheckAllNameConstraints`, `chromeLikelyIssued`,
`chromeValidChain`) and the curator-given Chrome helper predicates
(`Verdict.Policy.Chrome.isValidPki`, `strongSignature`, ...).

Each `spec_chrome_*` takes `impl : RepoImpl` and references the
Chrome APIs as `impl.verdict.chrome*`. Helper-predicate specs are
properties of fixed curator-given content and don't depend on
`impl`, but are parameterised on it for uniformity.

DO NOT MODIFY — this file is frozen curator-given content.

Upstream: `verdict/src/policy/chrome.rs` (ported from
`verdict_old/Verdict/Spec/Policy/Chrome.lean`).
-/

open Verdict.Policy

/-! ## § 1  Chrome validChain Decomposition -/

/-- Chrome `validChain` requires at least 2 certificates.
    Verus: `chain.len() >= 2` in `valid_chain`. -/
def spec_chrome_valid_chain_min_length (impl : RepoImpl) : Prop :=
  ∀ (env : Verdict.Policy.ChromePolicyEnv)
    (chain : List Verdict.Policy.AbstractCertificate)
    (task : Verdict.Policy.PolicyTask),
    impl.verdict.chromeValidChain env chain task = true →
    chain.length ≥ 2

/-- Chrome `validChain` verifies the leaf certificate.
    Verus: `cert_verified_leaf(env, task, chain[0], chain.last())`. -/
def spec_chrome_valid_chain_leaf (impl : RepoImpl) : Prop :=
  ∀ (env : Verdict.Policy.ChromePolicyEnv)
    (chain : List Verdict.Policy.AbstractCertificate)
    (task : Verdict.Policy.PolicyTask),
    impl.verdict.chromeValidChain env chain task = true →
    chain.length ≥ 2 →
    impl.verdict.chromeCertVerifiedLeaf env task
      chain[0]! chain[chain.length - 1]! = true

/-- Chrome `validChain` checks name constraints.
    Verus: `check_all_name_constraints(chain)`. -/
def spec_chrome_valid_chain_name_constraints (impl : RepoImpl) : Prop :=
  ∀ (env : Verdict.Policy.ChromePolicyEnv)
    (chain : List Verdict.Policy.AbstractCertificate)
    (task : Verdict.Policy.PolicyTask),
    impl.verdict.chromeValidChain env chain task = true →
    impl.verdict.chromeCheckAllNameConstraints chain = true

/-! ## § 2  Chrome likelyIssued Decomposition -/

/-- Chrome `likelyIssued` decomposes into normalized DN matching.
    Verus: `sameDN(issuer.subject, subject.issuer, true)` (chrome.rs:595). -/
def spec_chrome_likely_issued_decompose (impl : RepoImpl) : Prop :=
  ∀ (issuer subject : Verdict.Policy.AbstractCertificate),
    impl.verdict.chromeLikelyIssued issuer subject = true →
    Verdict.Policy.sameDN issuer.subject subject.issuer true = true

/-! ## § 3  Chrome Helper Predicate Properties (Curator-Given) -/

/-- `isValidPki` rejects DSA keys. -/
def spec_chrome_is_valid_pki_no_dsa (_impl : RepoImpl) : Prop :=
  ∀ (cert : Verdict.Policy.AbstractCertificate) (p q g : Nat),
    cert.subjectKey = .dsa p q g →
    Verdict.Policy.Chrome.isValidPki cert = false

/-- `strongSignature` accepts RSA+SHA256. -/
def spec_chrome_strong_signature_rsa_sha256 (_impl : RepoImpl) : Prop :=
  Verdict.Policy.Chrome.strongSignature "1.2.840.113549.1.1.11" = true
