import Verdict.Harness

/-!
# Verdict.Spec.PolicyOpenSSL

Specifications for OpenSSL-specific policy APIs (`opensslValidLeaf`,
`opensslValidIntermediate`, `opensslValidRoot`,
`opensslCheckNameConstraints`, `opensslCheckHostname`,
`opensslLikelyIssued`, `opensslValidChain`) and the curator-given
OpenSSL helper predicates (`Verdict.Policy.OpenSSL.checkCertKeyLevel`,
`checkCertTime`, `checkSan`, ...).

Each `spec_openssl_*` takes `impl : RepoImpl` and references the
OpenSSL APIs as `impl.verdict.openssl*`. Helper-predicate specs are
properties of fixed curator-given content and don't depend on
`impl`, but are parameterised on it for uniformity.

Note: OpenSSL has no policy environment — it is a unit policy with
fixed rules (unlike Chrome's `ChromePolicyEnv` or Firefox's
`FirefoxPolicyEnv`).

DO NOT MODIFY — this file is frozen curator-given content.

Upstream: `verdict/src/policy/openssl.rs` (ported from
`verdict_old/Verdict/Spec/Policy/OpenSSL.lean`).
-/

open Verdict.Policy

/-! ## § 1  OpenSSL validChain Decomposition -/

/-- OpenSSL `validChain` requires at least 2 certificates.
    Verus: `chain.len() >= 2` in `valid_chain` (openssl.rs:529). -/
def spec_openssl_valid_chain_min_length (impl : RepoImpl) : Prop :=
  ∀ (chain : List Verdict.Policy.AbstractCertificate)
    (task : Verdict.Policy.PolicyTask),
    impl.verdict.opensslValidChain chain task = true →
    chain.length ≥ 2

/-- OpenSSL `validChain` checks hostname when specified.
    Verus: `task.hostname matches Some(h) ==> check_hostname(chain[0], h)`
    in `valid_chain` (openssl.rs:529). -/
def spec_openssl_valid_chain_hostname (impl : RepoImpl) : Prop :=
  ∀ (chain : List Verdict.Policy.AbstractCertificate)
    (task : Verdict.Policy.PolicyTask) (hostname : String),
    impl.verdict.opensslValidChain chain task = true →
    task.hostname = some hostname →
    impl.verdict.opensslCheckHostname chain[0]! hostname = true

/-! ## § 2  OpenSSL likelyIssued Decomposition -/

/-- OpenSSL `likelyIssued` decomposes into normalized DN matching + AKI check.
    Verus: `sameDN(issuer.subject, subject.issuer, true) &&
            checkAuthKeyId(issuer, subject)` (openssl.rs:540). -/
def spec_openssl_likely_issued_decompose (impl : RepoImpl) : Prop :=
  ∀ (issuer subject : Verdict.Policy.AbstractCertificate),
    impl.verdict.opensslLikelyIssued issuer subject = true →
    Verdict.Policy.sameDN issuer.subject subject.issuer true = true ∧
    Verdict.Policy.checkAuthKeyId issuer subject = true

/-! ## § 3  OpenSSL Helper Predicate Properties (Curator-Given) -/

/-- `checkCertKeyLevel` accepts RSA keys ≥ 1024 bits. -/
def spec_openssl_check_cert_key_level_rsa (_impl : RepoImpl) : Prop :=
  ∀ (cert : Verdict.Policy.AbstractCertificate) (n : Nat),
    cert.subjectKey = .rsa n → n ≥ 1024 →
    Verdict.Policy.OpenSSL.checkCertKeyLevel cert = true

/-- `checkCertTime` validates time bounds correctly:
    accepts when `notBefore ≤ now < notAfter`. -/
def spec_openssl_check_cert_time_valid (_impl : RepoImpl) : Prop :=
  ∀ (cert : Verdict.Policy.AbstractCertificate) (now : UInt64),
    cert.notBefore ≤ now → cert.notAfter > now →
    Verdict.Policy.OpenSSL.checkCertTime cert now = true

/-- `checkSan` accepts certificates without a SAN extension. -/
def spec_openssl_check_san_none (_impl : RepoImpl) : Prop :=
  ∀ (cert : Verdict.Policy.AbstractCertificate),
    cert.extSubjectAltName = none →
    Verdict.Policy.OpenSSL.checkSan cert = true
