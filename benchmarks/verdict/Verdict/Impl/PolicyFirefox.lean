import Verdict.Impl.PolicyCommon
import Verdict.Impl.PolicyChrome

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Verdict.Impl.PolicyFirefox

Lean 4 port of `verdict/src/policy/firefox.rs` — the Firefox
NSS-based certificate validation policy. Ports
`verdict_old/Verdict/Policy/Firefox.lean` into the new-format layout.

Shape:

* Curator-given: `FirefoxPolicyEnv` struct and the five helper
  predicates (`checkEkuLeaf`, `checkKeyUsageLeaf`,
  `checkKeyUsageIntermediate`, `strongSignature`, `sigAlgMatch`)
  live in `namespace Verdict.Policy.Firefox`. The last two are
  re-exports of their Chrome counterparts. Each helper takes
  `Verdict.Policy.AbstractCertificate` (not the parser-layer
  `Verdict.Certificate`).
* Benchmark tasks: six `!benchmark code` stubs
  (`firefoxCertVerifiedLeaf`, `firefoxCertVerifiedIntermediate`,
  `firefoxCertVerifiedRoot`, `firefoxCheckAllNameConstraints`,
  `firefoxLikelyIssued`, `firefoxValidChain`) flat-namespaced under
  `Verdict` with matching `*Sig` type abbreviations. Signatures
  use `Verdict.Policy.PolicyTask` in place of Verus's
  `InternalTask`.

Upstream: `verdict/src/policy/firefox.rs`.
-/

namespace Verdict.Policy

/-! ## § 1  Firefox Policy Environment -/

/-- Firefox policy environment. Similar to Chrome but with different
    trust anchors and international certificate restrictions (Tubitak,
    ANSSI).  Verus: `struct Policy` in `firefox.rs` internal module. -/
structure FirefoxPolicyEnv where
  /-- Certificate revocation list fingerprints -/
  crl : List String
  /-- Symantec root fingerprints (distrusted) -/
  symantecRoots : List String
  /-- Symantec exception fingerprints -/
  symantecExceptions : List String
  /-- Tubitak root fingerprints (restricted issuer) -/
  tubitakFingerprints : List String
  /-- Tubitak restricted domains -/
  tubitakDomains : List String
  /-- ANSSI root fingerprints (restricted issuer) -/
  anssiFingerprints : List String
  /-- ANSSI restricted domains -/
  anssiDomains : List String
  deriving Inhabited

end Verdict.Policy

/-! ## § 2  Firefox Helper Predicates (Curator-Given) -/

namespace Verdict.Policy.Firefox

open Verdict.Policy

/-- Firefox leaf EKU check. Must have serverAuth, or no EKU extension.
    Verus: `check_eku_leaf` in `firefox.rs`. -/
def checkEkuLeaf (cert : AbstractCertificate) : Bool :=
  match cert.extExtendedKeyUsage with
  | none => true
  | some eku => eku.usages.any fun u => match u with
    | .serverAuth => true
    | _ => false

/-- Firefox leaf key usage check.
    Verus: `check_key_usage_leaf` in `firefox.rs`. -/
def checkKeyUsageLeaf (cert : AbstractCertificate) : Bool :=
  match cert.extKeyUsage with
  | none => true
  | some ku => ku.digitalSignature || ku.keyEncipherment || ku.keyAgreement

/-- Firefox intermediate key usage check. Must have keyCertSign.
    Verus: `check_key_usage_intermediate` in `firefox.rs`. -/
def checkKeyUsageIntermediate (cert : AbstractCertificate) : Bool :=
  match cert.extKeyUsage with
  | none => true
  | some ku => ku.keyCertSign

/-- Strong signature — re-export of Chrome's `strongSignature`.
    Verus: `strong_signature` (firefox.rs:180). -/
def strongSignature := Verdict.Policy.Chrome.strongSignature

/-- Signature algorithm OIDs match — re-export of Chrome's `sigAlgMatch`. -/
def sigAlgMatch := Verdict.Policy.Chrome.sigAlgMatch

end Verdict.Policy.Firefox

/-! ## § 3  API Signatures (DO NOT MODIFY) -/

namespace Verdict

/-- Verify a leaf certificate under Firefox policy. The extra `ev : Bool`
    flag distinguishes Extended-Validation leaves.
    Verus: `cert_verified_leaf` (firefox.rs:574). -/
abbrev FirefoxCertVerifiedLeafSig :=
  Verdict.Policy.FirefoxPolicyEnv → Verdict.Policy.PolicyTask →
    Verdict.Policy.AbstractCertificate → Bool → Bool

/-- Verify an intermediate certificate under Firefox policy.
    Verus: `cert_verified_intermediate` (firefox.rs:566). -/
abbrev FirefoxCertVerifiedIntermediateSig :=
  Verdict.Policy.FirefoxPolicyEnv → Verdict.Policy.PolicyTask →
    Verdict.Policy.AbstractCertificate → Verdict.Policy.AbstractCertificate →
    Nat → Bool

/-- Verify a root certificate under Firefox policy. Unlike Chrome, Firefox
    passes both the last intermediate and the leaf through so Tubitak/ANSSI
    domain restrictions can be enforced against the leaf.
    Verus: `cert_verified_root` (firefox.rs:440). -/
abbrev FirefoxCertVerifiedRootSig :=
  Verdict.Policy.FirefoxPolicyEnv → Verdict.Policy.PolicyTask →
    Verdict.Policy.AbstractCertificate → Verdict.Policy.AbstractCertificate →
    Verdict.Policy.AbstractCertificate → Nat → Bool

/-- Check name constraints across the chain.
    Verus: `check_all_name_constraints` (firefox.rs:615). -/
abbrev FirefoxCheckAllNameConstraintsSig :=
  List Verdict.Policy.AbstractCertificate → Bool

/-- Firefox `likely_issued`: exact (un-normalized) DN match + AKI check.
    Verus: `likely_issued` (firefox.rs:638). -/
abbrev FirefoxLikelyIssuedSig :=
  Verdict.Policy.AbstractCertificate → Verdict.Policy.AbstractCertificate → Bool

/-- Firefox `valid_chain`: compose per-cert checks + name constraints.
    Verus: `valid_chain` (firefox.rs:625). -/
abbrev FirefoxValidChainSig :=
  Verdict.Policy.FirefoxPolicyEnv → List Verdict.Policy.AbstractCertificate →
    Verdict.Policy.PolicyTask → Bool

end Verdict

-- !benchmark @start global_aux
-- !benchmark @end global_aux

/-! ## § 4  Firefox Per-Certificate Verification (LLM Implements) -/

-- !benchmark @start code_aux def=firefoxCertVerifiedLeaf
-- !benchmark @end code_aux def=firefoxCertVerifiedLeaf

def Verdict.firefoxCertVerifiedLeaf : Verdict.FirefoxCertVerifiedLeafSig :=
-- !benchmark @start code def=firefoxCertVerifiedLeaf
  sorry
-- !benchmark @end code def=firefoxCertVerifiedLeaf

-- !benchmark @start code_aux def=firefoxCertVerifiedIntermediate
-- !benchmark @end code_aux def=firefoxCertVerifiedIntermediate

def Verdict.firefoxCertVerifiedIntermediate : Verdict.FirefoxCertVerifiedIntermediateSig :=
-- !benchmark @start code def=firefoxCertVerifiedIntermediate
  sorry
-- !benchmark @end code def=firefoxCertVerifiedIntermediate

-- !benchmark @start code_aux def=firefoxCertVerifiedRoot
-- !benchmark @end code_aux def=firefoxCertVerifiedRoot

def Verdict.firefoxCertVerifiedRoot : Verdict.FirefoxCertVerifiedRootSig :=
-- !benchmark @start code def=firefoxCertVerifiedRoot
  sorry
-- !benchmark @end code def=firefoxCertVerifiedRoot

-- !benchmark @start code_aux def=firefoxCheckAllNameConstraints
-- !benchmark @end code_aux def=firefoxCheckAllNameConstraints

def Verdict.firefoxCheckAllNameConstraints : Verdict.FirefoxCheckAllNameConstraintsSig :=
-- !benchmark @start code def=firefoxCheckAllNameConstraints
  sorry
-- !benchmark @end code def=firefoxCheckAllNameConstraints

/-! ## § 5  Firefox Policy Composition (LLM Implements) -/

-- !benchmark @start code_aux def=firefoxLikelyIssued
-- !benchmark @end code_aux def=firefoxLikelyIssued

def Verdict.firefoxLikelyIssued : Verdict.FirefoxLikelyIssuedSig :=
-- !benchmark @start code def=firefoxLikelyIssued
  sorry
-- !benchmark @end code def=firefoxLikelyIssued

-- !benchmark @start code_aux def=firefoxValidChain
-- !benchmark @end code_aux def=firefoxValidChain

def Verdict.firefoxValidChain : Verdict.FirefoxValidChainSig :=
-- !benchmark @start code def=firefoxValidChain
  sorry
-- !benchmark @end code def=firefoxValidChain
