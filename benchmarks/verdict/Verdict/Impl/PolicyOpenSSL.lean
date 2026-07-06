import Verdict.Impl.PolicyCommon

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Verdict.Impl.PolicyOpenSSL

Lean 4 port of `verdict/src/policy/openssl.rs` — the OpenSSL
X.509 path validation policy. Ports `verdict_old/Verdict/Policy/OpenSSL.lean`
into the new-format layout.

Note: OpenSSL has no policy environment — it is a **unit policy**
with fixed rules. The Verus source declares `struct Policy;` (a
unit struct) and the Lean API signatures therefore take no env
argument (unlike Chrome's `ChromePolicyEnv` or Firefox's
`FirefoxPolicyEnv`).

Shape:

* Curator-given: seven helper predicates (`checkCertKeyLevel`,
  `checkCertTime`, `checkCa`, `checkBasicConstraints`,
  `checkKeyUsage`, `checkSan`, `checkDuplicateExts`) live in
  `namespace Verdict.Policy.OpenSSL`. Each takes
  `Verdict.Policy.AbstractCertificate` (not the parser-layer
  `Verdict.Certificate`). `checkDuplicateExts` is a re-export of
  `Verdict.Policy.checkDuplicateExtensions`.
* Benchmark tasks: seven `!benchmark code` stubs
  (`opensslValidLeaf`, `opensslValidIntermediate`, `opensslValidRoot`,
  `opensslCheckNameConstraints`, `opensslCheckHostname`,
  `opensslLikelyIssued`, `opensslValidChain`) flat-namespaced under
  `Verdict` with matching `*Sig` type abbreviations. Signatures
  use `Verdict.Policy.PolicyTask` in place of Verus's `InternalTask`.

Upstream: `verdict/src/policy/openssl.rs`.
-/

/-! ## § 1  OpenSSL Helper Predicates (Curator-Given) -/

namespace Verdict.Policy.OpenSSL

open Verdict.Policy

/-- Check certificate key security level (≥80 bits ⟹ RSA ≥ 1024).
    Verus: `check_cert_key_level` (openssl.rs:128). -/
def checkCertKeyLevel (cert : AbstractCertificate) : Bool :=
  match cert.subjectKey with
  | .rsa modLength => modLength ≥ 1024
  | _ => true

/-- Check certificate time validity against current time.
    Verus: `check_cert_time` (openssl.rs:141). -/
def checkCertTime (cert : AbstractCertificate) (now : UInt64) : Bool :=
  cert.notBefore ≤ now && cert.notAfter > now

/-- OpenSSL CA classification (0=notCA, 1=CA, 2=other).
    Verus: `check_ca` (openssl.rs:158). -/
def checkCa (cert : AbstractCertificate) : UInt32 :=
  if cert.extKeyUsage.any (fun ku => !ku.keyCertSign) then 0
  else if cert.extBasicConstraints.any (fun bc => bc.isCA) then 1
  else if cert.extBasicConstraints.any (fun bc => !bc.isCA) then 0
  else if cert.version == 1 || cert.extKeyUsage.isSome then 2
  else 0

/-- Check basic constraints validity.
    Verus: `check_basic_constraints` (openssl.rs:174). -/
def checkBasicConstraints (cert : AbstractCertificate) : Bool :=
  match cert.extBasicConstraints with
  | none => true
  | some bc =>
    (match bc.pathLen with
     | some _ => bc.isCA && cert.extKeyUsage.any (fun ku => ku.keyCertSign)
     | none => true) &&
    (if bc.isCA then bc.critical == some true else true)

/-- Check key usage for CA vs end-entity.
    Verus: `check_key_usage` (openssl.rs:187). -/
def checkKeyUsage (cert : AbstractCertificate) : Bool :=
  match cert.extBasicConstraints with
  | some bc =>
    if bc.isCA then cert.extKeyUsage.isSome
    else match cert.extKeyUsage with
         | some ku => !ku.keyCertSign
         | none => true
  | none => match cert.extKeyUsage with
            | some ku => !ku.keyCertSign
            | none => true

/-- Check SAN is non-empty if present.
    Verus: `check_san` (openssl.rs:197). -/
def checkSan (cert : AbstractCertificate) : Bool :=
  match cert.extSubjectAltName with
  | none => true
  | some san => san.names.length > 0

/-- No duplicate extension OIDs — alias for `Verdict.Policy.checkDuplicateExtensions`. -/
def checkDuplicateExts := Verdict.Policy.checkDuplicateExtensions

end Verdict.Policy.OpenSSL

/-! ## § 2  API Signatures (DO NOT MODIFY) -/

namespace Verdict

/-- Verify a leaf certificate under OpenSSL policy.
    Verus: `valid_leaf` (openssl.rs ~350). -/
abbrev OpensslValidLeafSig :=
  Verdict.Policy.PolicyTask → Verdict.Policy.AbstractCertificate → Bool

/-- Verify an intermediate certificate under OpenSSL policy.
    Verus: `valid_intermediate` (openssl.rs ~380). -/
abbrev OpensslValidIntermediateSig :=
  Verdict.Policy.PolicyTask → Verdict.Policy.AbstractCertificate → Nat → Bool

/-- Verify a root certificate under OpenSSL policy.
    Verus: `valid_root` (openssl.rs ~410). -/
abbrev OpensslValidRootSig :=
  Verdict.Policy.PolicyTask → Verdict.Policy.AbstractCertificate → Nat → Bool

/-- Check name constraints across the OpenSSL chain.
    Verus: `check_name_constraints` in `openssl.rs`. -/
abbrev OpensslCheckNameConstraintsSig :=
  List Verdict.Policy.AbstractCertificate → Bool

/-- Check hostname against leaf certificate SAN.
    Verus: `check_hostname` (openssl.rs ~470). -/
abbrev OpensslCheckHostnameSig :=
  Verdict.Policy.AbstractCertificate → String → Bool

/-- OpenSSL `likely_issued`: DN match (normalized) + AKI check.
    Verus: `likely_issued` (openssl.rs:540). -/
abbrev OpensslLikelyIssuedSig :=
  Verdict.Policy.AbstractCertificate → Verdict.Policy.AbstractCertificate → Bool

/-- OpenSSL `valid_chain`: compose per-cert checks, name constraints,
    and hostname matching.
    Verus: `valid_chain` (openssl.rs:529). -/
abbrev OpensslValidChainSig :=
  List Verdict.Policy.AbstractCertificate → Verdict.Policy.PolicyTask → Bool

end Verdict

-- !benchmark @start global_aux
-- !benchmark @end global_aux

/-! ## § 3  OpenSSL Per-Certificate Verification (LLM Implements) -/

-- !benchmark @start code_aux def=opensslValidLeaf
-- !benchmark @end code_aux def=opensslValidLeaf

def Verdict.opensslValidLeaf : Verdict.OpensslValidLeafSig :=
-- !benchmark @start code def=opensslValidLeaf
  sorry
-- !benchmark @end code def=opensslValidLeaf

-- !benchmark @start code_aux def=opensslValidIntermediate
-- !benchmark @end code_aux def=opensslValidIntermediate

def Verdict.opensslValidIntermediate : Verdict.OpensslValidIntermediateSig :=
-- !benchmark @start code def=opensslValidIntermediate
  sorry
-- !benchmark @end code def=opensslValidIntermediate

-- !benchmark @start code_aux def=opensslValidRoot
-- !benchmark @end code_aux def=opensslValidRoot

def Verdict.opensslValidRoot : Verdict.OpensslValidRootSig :=
-- !benchmark @start code def=opensslValidRoot
  sorry
-- !benchmark @end code def=opensslValidRoot

-- !benchmark @start code_aux def=opensslCheckNameConstraints
-- !benchmark @end code_aux def=opensslCheckNameConstraints

def Verdict.opensslCheckNameConstraints : Verdict.OpensslCheckNameConstraintsSig :=
-- !benchmark @start code def=opensslCheckNameConstraints
  sorry
-- !benchmark @end code def=opensslCheckNameConstraints

-- !benchmark @start code_aux def=opensslCheckHostname
-- !benchmark @end code_aux def=opensslCheckHostname

def Verdict.opensslCheckHostname : Verdict.OpensslCheckHostnameSig :=
-- !benchmark @start code def=opensslCheckHostname
  sorry
-- !benchmark @end code def=opensslCheckHostname

/-! ## § 4  OpenSSL Policy Composition (LLM Implements) -/

-- !benchmark @start code_aux def=opensslLikelyIssued
-- !benchmark @end code_aux def=opensslLikelyIssued

def Verdict.opensslLikelyIssued : Verdict.OpensslLikelyIssuedSig :=
-- !benchmark @start code def=opensslLikelyIssued
  sorry
-- !benchmark @end code def=opensslLikelyIssued

-- !benchmark @start code_aux def=opensslValidChain
-- !benchmark @end code_aux def=opensslValidChain

def Verdict.opensslValidChain : Verdict.OpensslValidChainSig :=
-- !benchmark @start code def=opensslValidChain
  sorry
-- !benchmark @end code def=opensslValidChain
