import Verdict.Harness
import Verdict.Impl.PolicyStandard

/-!
# Verdict.Spec.PolicyStandard

RFC 5280 conformance instantiations for each concrete policy
(Chrome, Firefox, OpenSSL). Each `spec_*` takes `impl : RepoImpl`
and states that the relevant `impl.verdict.*ValidChain` satisfies
one of the `Verdict.Policy.Standard` trait predicates.

Chrome and Firefox's `validChain` take a policy env (`ChromePolicyEnv`
/ `FirefoxPolicyEnv`) before `(chain, task)`, so each `spec_*` is
universally quantified over the env and then applies the partially
applied `validChain env`. OpenSSL's `validChain` already matches
`List AbstractCertificate → PolicyTask → Bool` directly.

DO NOT MODIFY — this file is frozen curator-given content.

Upstream: `verdict/src/policy/standard.rs` (ported from
`verdict_old/Verdict/Spec/Policy/Standard.lean`).
-/

open Verdict.Policy
open Verdict.Policy.Standard

/-! ## § 1  Chrome Conformance -/

def spec_chrome_time_validity (impl : RepoImpl) : Prop :=
  ∀ (env : Verdict.Policy.ChromePolicyEnv),
    TimeValidity (impl.verdict.chromeValidChain env)

def spec_chrome_sig_alg_consistency (impl : RepoImpl) : Prop :=
  ∀ (env : Verdict.Policy.ChromePolicyEnv),
    SigAlgConsistency (impl.verdict.chromeValidChain env)

def spec_chrome_basic_constraints_ca (impl : RepoImpl) : Prop :=
  ∀ (env : Verdict.Policy.ChromePolicyEnv),
    BasicConstraintsCA (impl.verdict.chromeValidChain env)

def spec_chrome_path_length_enforced (impl : RepoImpl) : Prop :=
  ∀ (env : Verdict.Policy.ChromePolicyEnv),
    PathLengthEnforced (impl.verdict.chromeValidChain env)

def spec_chrome_key_usage_ca (impl : RepoImpl) : Prop :=
  ∀ (env : Verdict.Policy.ChromePolicyEnv),
    KeyUsageCA (impl.verdict.chromeValidChain env)

def spec_chrome_key_usage_leaf (impl : RepoImpl) : Prop :=
  ∀ (env : Verdict.Policy.ChromePolicyEnv),
    KeyUsageLeaf (impl.verdict.chromeValidChain env)

def spec_chrome_extended_key_usage_leaf (impl : RepoImpl) : Prop :=
  ∀ (env : Verdict.Policy.ChromePolicyEnv),
    ExtendedKeyUsageLeaf (impl.verdict.chromeValidChain env)

def spec_chrome_unique_extensions (impl : RepoImpl) : Prop :=
  ∀ (env : Verdict.Policy.ChromePolicyEnv),
    UniqueExtensions (impl.verdict.chromeValidChain env)

def spec_chrome_strong_signature (impl : RepoImpl) : Prop :=
  ∀ (env : Verdict.Policy.ChromePolicyEnv),
    StrongSignature (impl.verdict.chromeValidChain env) Verdict.Policy.Chrome.strongSignature

def spec_chrome_valid_pki (impl : RepoImpl) : Prop :=
  ∀ (env : Verdict.Policy.ChromePolicyEnv),
    ValidPKI (impl.verdict.chromeValidChain env) Verdict.Policy.Chrome.isValidPki

def spec_chrome_chain_min_length (impl : RepoImpl) : Prop :=
  ∀ (env : Verdict.Policy.ChromePolicyEnv),
    ChainMinLength (impl.verdict.chromeValidChain env)

def spec_chrome_name_constraints_respected (impl : RepoImpl) : Prop :=
  ∀ (env : Verdict.Policy.ChromePolicyEnv),
    NameConstraintsRespected (impl.verdict.chromeValidChain env)
      impl.verdict.chromeCheckAllNameConstraints

def spec_chrome_authority_key_id_valid (impl : RepoImpl) : Prop :=
  ∀ (env : Verdict.Policy.ChromePolicyEnv),
    AuthorityKeyIdValid (impl.verdict.chromeValidChain env)

def spec_chrome_not_revoked (impl : RepoImpl) : Prop :=
  ∀ (env : Verdict.Policy.ChromePolicyEnv),
    NotRevoked (impl.verdict.chromeValidChain env) (Verdict.Policy.Chrome.notInCrl env)

def spec_chrome_subject_alt_name_present (impl : RepoImpl) : Prop :=
  ∀ (env : Verdict.Policy.ChromePolicyEnv),
    SubjectAltNamePresent (impl.verdict.chromeValidChain env)

def spec_chrome_valid_version (impl : RepoImpl) : Prop :=
  ∀ (env : Verdict.Policy.ChromePolicyEnv),
    ValidVersion (impl.verdict.chromeValidChain env)

/-! ## § 2  Firefox Conformance -/

def spec_firefox_time_validity (impl : RepoImpl) : Prop :=
  ∀ (env : Verdict.Policy.FirefoxPolicyEnv),
    TimeValidity (impl.verdict.firefoxValidChain env)

def spec_firefox_sig_alg_consistency (impl : RepoImpl) : Prop :=
  ∀ (env : Verdict.Policy.FirefoxPolicyEnv),
    SigAlgConsistency (impl.verdict.firefoxValidChain env)

def spec_firefox_basic_constraints_ca (impl : RepoImpl) : Prop :=
  ∀ (env : Verdict.Policy.FirefoxPolicyEnv),
    BasicConstraintsCA (impl.verdict.firefoxValidChain env)

def spec_firefox_path_length_enforced (impl : RepoImpl) : Prop :=
  ∀ (env : Verdict.Policy.FirefoxPolicyEnv),
    PathLengthEnforced (impl.verdict.firefoxValidChain env)

def spec_firefox_key_usage_ca (impl : RepoImpl) : Prop :=
  ∀ (env : Verdict.Policy.FirefoxPolicyEnv),
    KeyUsageCA (impl.verdict.firefoxValidChain env)

def spec_firefox_key_usage_leaf (impl : RepoImpl) : Prop :=
  ∀ (env : Verdict.Policy.FirefoxPolicyEnv),
    KeyUsageLeaf (impl.verdict.firefoxValidChain env)

def spec_firefox_extended_key_usage_leaf (impl : RepoImpl) : Prop :=
  ∀ (env : Verdict.Policy.FirefoxPolicyEnv),
    ExtendedKeyUsageLeaf (impl.verdict.firefoxValidChain env)

def spec_firefox_unique_extensions (impl : RepoImpl) : Prop :=
  ∀ (env : Verdict.Policy.FirefoxPolicyEnv),
    UniqueExtensions (impl.verdict.firefoxValidChain env)

def spec_firefox_strong_signature (impl : RepoImpl) : Prop :=
  ∀ (env : Verdict.Policy.FirefoxPolicyEnv),
    StrongSignature (impl.verdict.firefoxValidChain env) Verdict.Policy.Firefox.strongSignature

def spec_firefox_chain_min_length (impl : RepoImpl) : Prop :=
  ∀ (env : Verdict.Policy.FirefoxPolicyEnv),
    ChainMinLength (impl.verdict.firefoxValidChain env)

def spec_firefox_name_constraints_respected (impl : RepoImpl) : Prop :=
  ∀ (env : Verdict.Policy.FirefoxPolicyEnv),
    NameConstraintsRespected (impl.verdict.firefoxValidChain env)
      impl.verdict.firefoxCheckAllNameConstraints

def spec_firefox_authority_key_id_valid (impl : RepoImpl) : Prop :=
  ∀ (env : Verdict.Policy.FirefoxPolicyEnv),
    AuthorityKeyIdValid (impl.verdict.firefoxValidChain env)

def spec_firefox_subject_alt_name_present (impl : RepoImpl) : Prop :=
  ∀ (env : Verdict.Policy.FirefoxPolicyEnv),
    SubjectAltNamePresent (impl.verdict.firefoxValidChain env)

def spec_firefox_valid_version (impl : RepoImpl) : Prop :=
  ∀ (env : Verdict.Policy.FirefoxPolicyEnv),
    ValidVersion (impl.verdict.firefoxValidChain env)

/-! ## § 3  OpenSSL Conformance -/

def spec_openssl_time_validity (impl : RepoImpl) : Prop :=
  TimeValidity impl.verdict.opensslValidChain

def spec_openssl_sig_alg_consistency (impl : RepoImpl) : Prop :=
  SigAlgConsistency impl.verdict.opensslValidChain

def spec_openssl_basic_constraints_ca (impl : RepoImpl) : Prop :=
  BasicConstraintsCA impl.verdict.opensslValidChain

def spec_openssl_path_length_enforced (impl : RepoImpl) : Prop :=
  PathLengthEnforced impl.verdict.opensslValidChain

def spec_openssl_key_usage_ca (impl : RepoImpl) : Prop :=
  KeyUsageCA impl.verdict.opensslValidChain

def spec_openssl_key_usage_leaf (impl : RepoImpl) : Prop :=
  KeyUsageLeaf impl.verdict.opensslValidChain

def spec_openssl_unique_extensions (impl : RepoImpl) : Prop :=
  UniqueExtensions impl.verdict.opensslValidChain

def spec_openssl_chain_min_length (impl : RepoImpl) : Prop :=
  ChainMinLength impl.verdict.opensslValidChain

def spec_openssl_name_constraints_respected (impl : RepoImpl) : Prop :=
  NameConstraintsRespected impl.verdict.opensslValidChain
    impl.verdict.opensslCheckNameConstraints

def spec_openssl_authority_key_id_valid (impl : RepoImpl) : Prop :=
  AuthorityKeyIdValid impl.verdict.opensslValidChain

def spec_openssl_valid_pki (impl : RepoImpl) : Prop :=
  ValidPKI impl.verdict.opensslValidChain Verdict.Policy.OpenSSL.checkCertKeyLevel

def spec_openssl_subject_alt_name_present (impl : RepoImpl) : Prop :=
  SubjectAltNamePresent impl.verdict.opensslValidChain

def spec_openssl_hostname_match (impl : RepoImpl) : Prop :=
  HostnameMatch impl.verdict.opensslValidChain impl.verdict.opensslCheckHostname

def spec_openssl_valid_version (impl : RepoImpl) : Prop :=
  ValidVersion impl.verdict.opensslValidChain
