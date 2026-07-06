import Verdict.Impl.PolicyCommon

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Verdict.Impl.PolicyChrome

Lean 4 port of `verdict/src/policy/chrome.rs` — the Chrome
certificate-transparency and validation policy. Ports
`verdict_old/Verdict/Policy/Chrome.lean` into the new-format layout.

Shape:

* Curator-given: `ChromePolicyEnv` struct and the eight helper
  predicates (`isValidPki`, `isKnownRoot`, `leafDurationValid`,
  `notInCrl`, `strongSignature`, `keyUsageValid`,
  `extendedKeyUsageValid`, `sigAlgMatch`) live in
  `namespace Verdict.Policy.Chrome`. Each takes
  `Verdict.Policy.AbstractCertificate` (not the parser-layer
  `Verdict.Certificate`).
* Benchmark tasks: six `!benchmark code` stubs
  (`chromeCertVerifiedLeaf`, `chromeCertVerifiedIntermediate`,
  `chromeCertVerifiedRoot`, `chromeCheckAllNameConstraints`,
  `chromeLikelyIssued`, `chromeValidChain`) flat-namespaced under
  `Verdict` with matching `*Sig` type abbreviations. Signatures
  use `Verdict.Policy.PolicyTask` in place of Verus's
  `InternalTask`.

Upstream: `verdict/src/policy/chrome.rs`.
-/

namespace Verdict.Policy

/-! ## § 1  Chrome Policy Environment -/

/-- Chrome policy environment carrying root fingerprints and CRL data.
    Verus: `struct Policy` in `chrome.rs` internal module. -/
structure ChromePolicyEnv where
  /-- Public suffix list entries -/
  publicSuffix : List String
  /-- Certificate revocation list fingerprints -/
  crl : List String
  /-- Known root certificate fingerprints -/
  knownRoots : List String
  /-- Symantec root fingerprints (distrusted) -/
  symantecRoots : List String
  /-- Symantec exception fingerprints -/
  symantecExceptions : List String
  /-- India CCA trusted root fingerprints -/
  indiaTrusted : List String
  /-- India CCA restricted domains -/
  indiaDomains : List String
  /-- ANSSI trusted root fingerprints -/
  anssiTrusted : List String
  /-- ANSSI restricted domains -/
  anssiDomains : List String
  deriving Inhabited

end Verdict.Policy

/-! ## § 2  Chrome Helper Predicates (Curator-Given) -/

namespace Verdict.Policy.Chrome

open Verdict.Policy

/-- Valid PKI key type. Verus: `is_valid_pki` (chrome.rs:163). -/
def isValidPki (cert : AbstractCertificate) : Bool :=
  match cert.subjectKey with
  | .rsa modLength => modLength ≥ 1024
  | .dsa _ _ _ => false
  | .other => true

/-- Certificate fingerprint is in known roots list.
    Verus: `is_known_root` (chrome.rs:172). -/
def isKnownRoot (env : ChromePolicyEnv) (root : AbstractCertificate) : Bool :=
  env.knownRoots.any (· == root.fingerprint)

/-- Leaf certificate duration validity (tiered by issuance date).
    Verus: `leaf_duration_valid` (chrome.rs:178). -/
def leafDurationValid (cert : AbstractCertificate) : Bool :=
  cert.notBefore ≤ cert.notAfter && (
    let duration := cert.notAfter - cert.notBefore
    let july2012 : UInt64 := 1341100800
    let april2015 : UInt64 := 1427846400
    let march2018 : UInt64 := 1519862400
    let july2019 : UInt64 := 1561939200
    let sep2020 : UInt64 := 1598918400
    let tenYears : UInt64 := 315532800
    let sixtyMonths : UInt64 := 157852800
    let thirtyNineMonths : UInt64 := 102643200
    let eightTwentyFiveDays : UInt64 := 71280000
    let threeNinetyEightDays : UInt64 := 34387200
    (cert.notBefore < july2012 && cert.notAfter < july2019 && duration ≤ tenYears) ||
    (cert.notBefore ≥ july2012 && cert.notBefore < april2015 && duration ≤ sixtyMonths) ||
    (cert.notBefore ≥ april2015 && cert.notBefore < march2018 && duration ≤ thirtyNineMonths) ||
    (cert.notBefore ≥ march2018 && cert.notBefore < sep2020 && duration ≤ eightTwentyFiveDays) ||
    (cert.notBefore ≥ sep2020 && duration ≤ threeNinetyEightDays))

/-- Certificate not in CRL. Verus: `not_in_crl` (chrome.rs:202). -/
def notInCrl (env : ChromePolicyEnv) (cert : AbstractCertificate) : Bool :=
  env.crl.all (· != cert.fingerprint)

/-- Signature uses a strong algorithm (SHA-256+).
    Verus: `strong_signature` (chrome.rs:206). -/
def strongSignature (alg : String) : Bool :=
  alg == "1.2.840.10045.4.3.2" ||  -- ECDSA+SHA256
  alg == "1.2.840.10045.4.3.3" ||  -- ECDSA+SHA384
  alg == "1.2.840.10045.4.3.4" ||  -- ECDSA+SHA512
  alg == "1.2.840.113549.1.1.11" || -- RSA+SHA256
  alg == "1.2.840.113549.1.1.12" || -- RSA+SHA384
  alg == "1.2.840.113549.1.1.13" || -- RSA+SHA512
  alg == "1.2.840.113549.1.1.10"    -- RSA-PSS+SHA256

/-- Key usage valid per Chrome rules. Verus: `key_usage_valid` (chrome.rs:223). -/
def keyUsageValid (cert : AbstractCertificate) : Bool :=
  match cert.extKeyUsage with
  | none => true
  | some ku =>
    match cert.extBasicConstraints with
    | some bc => if bc.isCA then ku.keyCertSign
                 else !ku.keyCertSign && (ku.digitalSignature || ku.keyEncipherment || ku.keyAgreement)
    | none => !ku.keyCertSign && (ku.digitalSignature || ku.keyEncipherment || ku.keyAgreement)

/-- Extended key usage includes serverAuth or any.
    Verus: `extended_key_usage_valid` (chrome.rs:237). -/
def extendedKeyUsageValid (cert : AbstractCertificate) : Bool :=
  match cert.extExtendedKeyUsage with
  | none => true
  | some eku => eku.usages.any fun u => match u with
    | .serverAuth => true
    | .any => true
    | _ => false

/-- Inner/outer signature algorithm OIDs match.
    Verus: checked in `cert_verified_*`. -/
def sigAlgMatch (cert : AbstractCertificate) : Bool :=
  cert.sigAlgOuter.id == cert.sigAlgInner.id

end Verdict.Policy.Chrome

/-! ## § 3  API Signatures (DO NOT MODIFY) -/

namespace Verdict

/-- Verify a leaf certificate under Chrome policy.
    Verus: `cert_verified_leaf` (chrome.rs ~350-400). -/
abbrev ChromeCertVerifiedLeafSig :=
  Verdict.Policy.ChromePolicyEnv → Verdict.Policy.PolicyTask →
    Verdict.Policy.AbstractCertificate → Verdict.Policy.AbstractCertificate → Bool

/-- Verify an intermediate certificate under Chrome policy.
    Verus: `cert_verified_intermediate` (chrome.rs ~400-450). -/
abbrev ChromeCertVerifiedIntermediateSig :=
  Verdict.Policy.ChromePolicyEnv → Verdict.Policy.PolicyTask →
    Verdict.Policy.AbstractCertificate → Nat → Bool

/-- Verify a root certificate under Chrome policy.
    Verus: `cert_verified_root` (chrome.rs ~450-500). -/
abbrev ChromeCertVerifiedRootSig :=
  Verdict.Policy.ChromePolicyEnv → Verdict.Policy.PolicyTask →
    Verdict.Policy.AbstractCertificate → Verdict.Policy.AbstractCertificate → Nat → Bool

/-- Check name constraints across the chain.
    Verus: `check_all_name_constraints` (chrome.rs:571). -/
abbrev ChromeCheckAllNameConstraintsSig :=
  List Verdict.Policy.AbstractCertificate → Bool

/-- Chrome `likely_issued`: DN match only, no AKI check.
    Verus: `likely_issued` (chrome.rs:595). -/
abbrev ChromeLikelyIssuedSig :=
  Verdict.Policy.AbstractCertificate → Verdict.Policy.AbstractCertificate → Bool

/-- Chrome `valid_chain`: compose per-cert checks + name constraints.
    Verus: `valid_chain` (chrome.rs:582). -/
abbrev ChromeValidChainSig :=
  Verdict.Policy.ChromePolicyEnv → List Verdict.Policy.AbstractCertificate →
    Verdict.Policy.PolicyTask → Bool

end Verdict

-- !benchmark @start global_aux
-- !benchmark @end global_aux

/-! ## § 4  Chrome Per-Certificate Verification (LLM Implements) -/

-- !benchmark @start code_aux def=chromeCertVerifiedLeaf
-- !benchmark @end code_aux def=chromeCertVerifiedLeaf

def Verdict.chromeCertVerifiedLeaf : Verdict.ChromeCertVerifiedLeafSig :=
-- !benchmark @start code def=chromeCertVerifiedLeaf
  sorry
-- !benchmark @end code def=chromeCertVerifiedLeaf

-- !benchmark @start code_aux def=chromeCertVerifiedIntermediate
-- !benchmark @end code_aux def=chromeCertVerifiedIntermediate

def Verdict.chromeCertVerifiedIntermediate : Verdict.ChromeCertVerifiedIntermediateSig :=
-- !benchmark @start code def=chromeCertVerifiedIntermediate
  sorry
-- !benchmark @end code def=chromeCertVerifiedIntermediate

-- !benchmark @start code_aux def=chromeCertVerifiedRoot
-- !benchmark @end code_aux def=chromeCertVerifiedRoot

def Verdict.chromeCertVerifiedRoot : Verdict.ChromeCertVerifiedRootSig :=
-- !benchmark @start code def=chromeCertVerifiedRoot
  sorry
-- !benchmark @end code def=chromeCertVerifiedRoot

-- !benchmark @start code_aux def=chromeCheckAllNameConstraints
-- !benchmark @end code_aux def=chromeCheckAllNameConstraints

def Verdict.chromeCheckAllNameConstraints : Verdict.ChromeCheckAllNameConstraintsSig :=
-- !benchmark @start code def=chromeCheckAllNameConstraints
  sorry
-- !benchmark @end code def=chromeCheckAllNameConstraints

/-! ## § 5  Chrome Policy Composition (LLM Implements) -/

-- !benchmark @start code_aux def=chromeLikelyIssued
-- !benchmark @end code_aux def=chromeLikelyIssued

def Verdict.chromeLikelyIssued : Verdict.ChromeLikelyIssuedSig :=
-- !benchmark @start code def=chromeLikelyIssued
  sorry
-- !benchmark @end code def=chromeLikelyIssued

-- !benchmark @start code_aux def=chromeValidChain
-- !benchmark @end code_aux def=chromeValidChain

def Verdict.chromeValidChain : Verdict.ChromeValidChainSig :=
-- !benchmark @start code def=chromeValidChain
  sorry
-- !benchmark @end code def=chromeValidChain
