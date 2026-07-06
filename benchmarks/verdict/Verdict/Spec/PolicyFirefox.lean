import Verdict.Harness

/-!
# Verdict.Spec.PolicyFirefox

Specifications for Firefox-specific policy APIs (`firefoxCertVerifiedLeaf`,
`firefoxCertVerifiedIntermediate`, `firefoxCertVerifiedRoot`,
`firefoxCheckAllNameConstraints`, `firefoxLikelyIssued`,
`firefoxValidChain`) and the curator-given Firefox helper predicates
(`Verdict.Policy.Firefox.checkEkuLeaf`, `checkKeyUsageLeaf`, ...).

Each `spec_firefox_*` takes `impl : RepoImpl` and references the
Firefox APIs as `impl.verdict.firefox*`. Helper-predicate specs are
properties of fixed curator-given content and don't depend on
`impl`, but are parameterised on it for uniformity.

DO NOT MODIFY — this file is frozen curator-given content.

Upstream: `verdict/src/policy/firefox.rs` (ported from
`verdict_old/Verdict/Spec/Policy/Firefox.lean`).
-/

open Verdict.Policy

/-! ## § 1  Firefox validChain Decomposition -/

/-- Firefox `validChain` requires at least 2 certificates.
    Verus: `chain.len() >= 2` in `valid_chain` (firefox.rs:625). -/
def spec_firefox_valid_chain_min_length (impl : RepoImpl) : Prop :=
  ∀ (env : Verdict.Policy.FirefoxPolicyEnv)
    (chain : List Verdict.Policy.AbstractCertificate)
    (task : Verdict.Policy.PolicyTask),
    impl.verdict.firefoxValidChain env chain task = true →
    chain.length ≥ 2

/-- Firefox `validChain` checks name constraints.
    Verus: `check_all_name_constraints(chain)` (firefox.rs:625). -/
def spec_firefox_valid_chain_name_constraints (impl : RepoImpl) : Prop :=
  ∀ (env : Verdict.Policy.FirefoxPolicyEnv)
    (chain : List Verdict.Policy.AbstractCertificate)
    (task : Verdict.Policy.PolicyTask),
    impl.verdict.firefoxValidChain env chain task = true →
    impl.verdict.firefoxCheckAllNameConstraints chain = true

/-! ## § 2  Firefox likelyIssued Decomposition -/

/-- Firefox `likelyIssued` decomposes into exact (un-normalized) DN matching
    and an Authority-Key-Identifier check — unlike Chrome which normalizes
    and skips the AKI check.
    Verus: `sameDN(issuer.subject, subject.issuer, false) &&
            checkAuthKeyId(issuer, subject)` (firefox.rs:638). -/
def spec_firefox_likely_issued_decompose (impl : RepoImpl) : Prop :=
  ∀ (issuer subject : Verdict.Policy.AbstractCertificate),
    impl.verdict.firefoxLikelyIssued issuer subject = true →
    Verdict.Policy.sameDN issuer.subject subject.issuer false = true ∧
    Verdict.Policy.checkAuthKeyId issuer subject = true

/-! ## § 3  Firefox Helper Predicate Properties (Curator-Given) -/

/-- Firefox EKU check accepts certs with no EKU extension. -/
def spec_firefox_check_eku_leaf_none (_impl : RepoImpl) : Prop :=
  ∀ (cert : Verdict.Policy.AbstractCertificate),
    cert.extExtendedKeyUsage = none →
    Verdict.Policy.Firefox.checkEkuLeaf cert = true

/-- Firefox leaf key usage check accepts certs with no key usage extension. -/
def spec_firefox_check_key_usage_leaf_none (_impl : RepoImpl) : Prop :=
  ∀ (cert : Verdict.Policy.AbstractCertificate),
    cert.extKeyUsage = none →
    Verdict.Policy.Firefox.checkKeyUsageLeaf cert = true
