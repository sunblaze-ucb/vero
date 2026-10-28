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
def strongSignature (alg : String) : Bool :=
  Verdict.Policy.Chrome.strongSignature alg && alg != "1.2.840.113549.1.1.10"

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
namespace Verdict.Policy.Firefox
open Verdict.Policy

def isValidPki (cert : AbstractCertificate) : Bool :=
  match cert.subjectKey with
  | .rsa bits => bits ≥ 2048
  | .dsa _ _ _ => false
  | .other => true

def validName (name : String) : Bool :=
  if name.any (· == '*') then
    name.length > 2 && name.startsWith "*." && !name.endsWith "." &&
      (String.ofList (name.toList.drop 2)).any (· == '.')
  else !name.isEmpty && !name.startsWith "." && !name.endsWith "."

def matchCommonNameDomain (cert : AbstractCertificate) (name : String) : Bool :=
  cert.subject.rdns.any fun rdn => rdn.any fun a =>
    a.oid == "2.5.4.3" && validName a.value && matchName a.value name

def matchSanDomain (san : SubjectAltName) (name : String) : Bool :=
  san.names.all (fun n => match n with
    | .dnsName s => validName s | _ => true) &&
  san.names.any (fun n => match n with
    | .dnsName s => matchName s.toLower name | _ => false)

def checkUnhandledExtensions (cert : AbstractCertificate) : Bool :=
  cert.allExts.all fun es => es.all fun e =>
    e.critical != some true ||
      ["2.5.29.9", "2.5.29.14", "2.5.29.15", "2.5.29.16", "2.5.29.17", "2.5.29.18",
       "2.5.29.19", "2.5.29.30", "2.5.29.31", "2.5.29.32", "2.5.29.33", "2.5.29.36",
       "2.5.29.35", "2.5.29.37", "1.3.6.1.5.5.7.1.1"].contains e.oid

def extendedKeyUsageValid (cert : AbstractCertificate) : Bool :=
  cert.extExtendedKeyUsage.all fun eku =>
    eku.usages.contains .serverAuth &&
    (cert.extBasicConstraints.any (·.isCA) || !eku.usages.contains .ocspSigning)

def internationalValid (env : FirefoxPolicyEnv) (cert leaf : AbstractCertificate) : Bool :=
  leaf.extSubjectAltName.all fun san => san.names.all fun n => match n with
    | .dnsName name =>
      (!env.tubitakFingerprints.contains cert.fingerprint ||
        env.tubitakDomains.any (fun p => matchName p name)) &&
      (!env.anssiFingerprints.contains cert.fingerprint ||
        env.anssiDomains.any (fun p => matchName p name))
    | _ => true

def certVerifiedNonLeaf (env : FirefoxPolicyEnv) (task : PolicyTask)
    (cert leaf : AbstractCertificate) (depth : Nat) : Bool :=
  internationalValid env cert leaf && isValidPki cert && depth ≤ 6 &&
  cert.extBasicConstraints.any (fun bc => bc.isCA &&
    bc.pathLen.all (fun n => 0 ≤ n && (depth : Int) ≤ n)) &&
  cert.sigAlgInner.bytes == cert.sigAlgOuter.bytes &&
  cert.notBefore ≤ task.now && task.now ≤ cert.notAfter &&
  cert.extKeyUsage.all (fun ku => cert.extBasicConstraints.any (·.isCA) && ku.keyCertSign) &&
  cert.extAuthorityKeyId.all (fun aki => aki.critical != some true) &&
  !cert.subject.rdns.isEmpty && checkDuplicateExtensions cert && checkUnhandledExtensions cert &&
  cert.extSubjectKeyId.all (fun skid => skid.critical != some true)

def checkDnsNameConstraints (nc : NameConstraints) (name : String) : Bool :=
  let permits := nc.permitted.filterMap fun n => match n with
    | .dnsName s => some s | _ => none
  (permits.isEmpty || permits.any (fun p => permitName p name)) &&
  nc.excluded.all (fun n => match n with
    | .dnsName p => !permitName p name | _ => true)

def checkDirectoryNameConstraints (nc : NameConstraints) (name : DistinguishedName) : Bool :=
  let permits := nc.permitted.filterMap fun n => match n with
    | .directoryName dn => some dn | _ => none
  (permits.isEmpty || permits.any (fun p => isSubtreeOf p name false)) &&
  nc.excluded.all (fun n => match n with
    | .directoryName p => !isSubtreeOf p name false | _ => true)

def checkNameConstraints (cert target : AbstractCertificate) (isLeaf : Bool) : Bool :=
  cert.extNameConstraints.all fun nc =>
    (nc.permitted ++ nc.excluded).all (fun n => match n with
      | .dnsName name => !name.isEmpty && !name.endsWith "." && !name.any (· == '*')
      | _ => true) &&
    (!nc.permitted.isEmpty || !nc.excluded.isEmpty) &&
    target.extSubjectAltName.all (fun san => san.names.all fun n => match n with
      | .dnsName name => checkDnsNameConstraints nc name
      | .directoryName dn => checkDirectoryNameConstraints nc dn
      | .ipAddr addr => Chrome.checkIpNameConstraints nc addr
      | .otherName => false
      | _ => true) &&
    (!isLeaf || target.extSubjectAltName.isSome ||
      target.subject.rdns.all (fun rdn => rdn.all fun a =>
        a.oid != "2.5.4.3" || checkDnsNameConstraints nc a.value)) &&
    checkDirectoryNameConstraints nc target.subject

end Verdict.Policy.Firefox

-- !benchmark @end global_aux

/-! ## § 4  Firefox Per-Certificate Verification (LLM Implements) -/

-- !benchmark @start code_aux def=firefoxCertVerifiedLeaf
-- !benchmark @end code_aux def=firefoxCertVerifiedLeaf

def Verdict.firefoxCertVerifiedLeaf : Verdict.FirefoxCertVerifiedLeafSig :=
-- !benchmark @start code def=firefoxCertVerifiedLeaf
  fun env task cert ev =>
    Verdict.Policy.Firefox.isValidPki cert &&
    task.hostname.all (fun name => match cert.extSubjectAltName with
      | some san => Verdict.Policy.Firefox.matchSanDomain san name.toLower
      | none => Verdict.Policy.Firefox.matchCommonNameDomain cert name.toLower) &&
    cert.extBasicConstraints.all (fun bc => !bc.isCA) &&
    (!ev || (cert.notBefore ≤ cert.notAfter && cert.notAfter - cert.notBefore < 71712000)) &&
    !env.crl.contains cert.fingerprint && cert.sigAlgInner.bytes == cert.sigAlgOuter.bytes &&
    cert.notBefore ≤ task.now && task.now ≤ cert.notAfter &&
    Verdict.Policy.Firefox.strongSignature cert.sigAlgInner.id &&
    Verdict.Policy.Firefox.checkKeyUsageLeaf cert && Verdict.Policy.Firefox.extendedKeyUsageValid cert &&
    Verdict.Policy.checkDuplicateExtensions cert && Verdict.Policy.Firefox.checkUnhandledExtensions cert &&
    cert.extSubjectKeyId.all (fun skid => skid.critical != some true)
-- !benchmark @end code def=firefoxCertVerifiedLeaf

-- !benchmark @start code_aux def=firefoxCertVerifiedIntermediate
-- !benchmark @end code_aux def=firefoxCertVerifiedIntermediate

def Verdict.firefoxCertVerifiedIntermediate : Verdict.FirefoxCertVerifiedIntermediateSig :=
-- !benchmark @start code def=firefoxCertVerifiedIntermediate
  fun env task cert leaf depth =>
    Verdict.Policy.Firefox.certVerifiedNonLeaf env task cert leaf depth &&
    !env.crl.contains cert.fingerprint &&
    Verdict.Policy.Firefox.strongSignature cert.sigAlgInner.id &&
    Verdict.Policy.Firefox.extendedKeyUsageValid cert
-- !benchmark @end code def=firefoxCertVerifiedIntermediate

-- !benchmark @start code_aux def=firefoxCertVerifiedRoot
-- !benchmark @end code_aux def=firefoxCertVerifiedRoot

def Verdict.firefoxCertVerifiedRoot : Verdict.FirefoxCertVerifiedRootSig :=
-- !benchmark @start code def=firefoxCertVerifiedRoot
  fun env task cert interm leaf depth =>
    Verdict.Policy.Firefox.certVerifiedNonLeaf env task cert leaf depth &&
    (!env.symantecRoots.contains cert.fingerprint ||
      env.symantecExceptions.contains interm.fingerprint || cert.notBefore ≥ 1464739200) &&
    Verdict.Policy.Firefox.internationalValid env cert leaf
-- !benchmark @end code def=firefoxCertVerifiedRoot

-- !benchmark @start code_aux def=firefoxCheckAllNameConstraints
-- !benchmark @end code_aux def=firefoxCheckAllNameConstraints

def Verdict.firefoxCheckAllNameConstraints : Verdict.FirefoxCheckAllNameConstraintsSig :=
-- !benchmark @start code def=firefoxCheckAllNameConstraints
  fun chain =>
    !chain.isEmpty &&
    ((List.range (chain.length - 1)).map (· + 1)).all (fun i =>
      (List.range i).all (fun j =>
        Verdict.Policy.Firefox.checkNameConstraints chain[i]! chain[j]! (j == 0)))
-- !benchmark @end code def=firefoxCheckAllNameConstraints

/-! ## § 5  Firefox Policy Composition (LLM Implements) -/

-- !benchmark @start code_aux def=firefoxLikelyIssued
-- !benchmark @end code_aux def=firefoxLikelyIssued

def Verdict.firefoxLikelyIssued : Verdict.FirefoxLikelyIssuedSig :=
-- !benchmark @start code def=firefoxLikelyIssued
  fun issuer subject =>
    Verdict.Policy.sameDN issuer.subject subject.issuer false &&
    Verdict.Policy.checkAuthKeyId issuer subject
-- !benchmark @end code def=firefoxLikelyIssued

-- !benchmark @start code_aux def=firefoxValidChain
-- !benchmark @end code_aux def=firefoxValidChain

def Verdict.firefoxValidChain : Verdict.FirefoxValidChainSig :=
-- !benchmark @start code def=firefoxValidChain
  fun env chain task =>
    chain.length ≥ 2 &&
    Verdict.firefoxCertVerifiedLeaf env task chain[0]! false &&
    ((List.range (chain.length - 2)).map (· + 1)).all (fun i =>
      Verdict.firefoxCertVerifiedIntermediate env task chain[i]! chain[0]! (i - 1)) &&
    Verdict.firefoxCertVerifiedRoot env task chain[chain.length - 1]! chain[chain.length - 2]!
      chain[0]! (chain.length - 2) &&
    Verdict.firefoxCheckAllNameConstraints chain
-- !benchmark @end code def=firefoxValidChain
