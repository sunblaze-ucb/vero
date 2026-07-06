import Verdict.Impl.Asn1

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Verdict.Impl.PolicyCommon

Abstract policy-layer certificate representation + shared predicate
helpers used across Chrome / Firefox / OpenSSL and the validator's
chain-policy checks. Ported from `verdict_old/Verdict/Policy/Common.lean`
into the new-format layout.

All types + defs here are curator-given vocabulary (DO NOT MODIFY).
They are distinct from the parser-layer `Verdict.Certificate` (in
`Impl/Asn1.lean`, which mirrors Verus's `SpecCertificateValue`);
this module's `AbstractCertificate` mirrors Verus's
`policy::Certificate`.

Upstream: `verdict/src/policy/common.rs` +
`verdict/src/issue.rs` (normalize_string is aliased into
`policy/common.rs`).
-/

namespace Verdict.Policy

/-! ## § 1  String and Name Helpers -/

/-- An OID-and-value attribute in a Distinguished Name.
    Verus `rspec!`: `pub struct Attribute { pub oid: SpecString, pub value: SpecString }` -/
structure Attribute where
  oid   : String
  value : String
  deriving Repr, DecidableEq, Inhabited

/-- An X.509 Distinguished Name as an abstract sequence of RDNs,
    with attribute values decoded to strings.
    Verus `rspec!`: `pub struct DistinguishedName(pub Seq<Seq<Attribute>>)` -/
structure DistinguishedName where
  rdns : List (List Attribute)
  deriving Repr, DecidableEq, Inhabited

/-- A GeneralName as used in Subject Alternative Names and Name Constraints.
    Verus `rspec!`: `pub enum GeneralName { DNSName, DirectoryName, IPAddr, OtherName, Unsupported }` -/
inductive GeneralName where
  | dnsName       (name : String)
  | directoryName (dn   : DistinguishedName)
  | ipAddr        (addr : ByteArray)
  | otherName
  | unsupported
  deriving Inhabited

/-! ## § 2  Subject Public Key -/

/-- The type of the subject public key.
    Verus `rspec!`: `pub enum SubjectKey { RSA { mod_length }, DSA { ... }, Other }` -/
inductive SubjectKey where
  | rsa (modLength : Nat)
  | dsa (pLen qLen gLen : Nat)
  | other
  deriving Repr, DecidableEq, Inhabited

/-! ## § 3  Certificate Extensions -/

/-- RFC 5280 §4.2.1.1 Authority Key Identifier. -/
structure AuthorityKeyIdentifier where
  critical : Option Bool
  keyId    : Option String
  issuer   : Option String
  serial   : Option String
  deriving Repr, DecidableEq, Inhabited

/-- RFC 5280 §4.2.1.2 Subject Key Identifier. -/
structure SubjectKeyIdentifier where
  critical : Option Bool
  keyId    : String
  deriving Repr, DecidableEq, Inhabited

/-- Extended Key Usage purpose OIDs (RFC 5280 §4.2.1.12). -/
inductive ExtendedKeyUsageType where
  | serverAuth
  | clientAuth
  | codeSigning
  | emailProtection
  | timeStamping
  | ocspSigning
  | any
  | other (oid : String)
  deriving Repr, DecidableEq, Inhabited

/-- RFC 5280 §4.2.1.12 Extended Key Usage. -/
structure ExtendedKeyUsage where
  critical : Option Bool
  usages   : List ExtendedKeyUsageType
  deriving Repr, DecidableEq, Inhabited

/-- RFC 5280 §4.2.1.9 Basic Constraints. `isCA` is plain `Bool`
    (not `Option`) per the Verus source. -/
structure BasicConstraints where
  critical : Option Bool
  isCA     : Bool
  pathLen  : Option Int
  deriving Repr, DecidableEq, Inhabited

/-- RFC 5280 §4.2.1.3 Key Usage — all nine named bits. -/
structure KeyUsage where
  critical         : Option Bool
  digitalSignature : Bool
  nonRepudiation   : Bool
  keyEncipherment  : Bool
  dataEncipherment : Bool
  keyAgreement     : Bool
  keyCertSign      : Bool
  crlSign          : Bool
  encipherOnly     : Bool
  decipherOnly     : Bool
  deriving Repr, DecidableEq, Inhabited

/-- RFC 5280 §4.2.1.6 Subject Alternative Name. -/
structure SubjectAltName where
  critical : Option Bool
  names    : List GeneralName
  deriving Inhabited

/-- RFC 5280 §4.2.1.10 Name Constraints.
    Verus uses flat `permitted`/`excluded` sequences (not `Option`). -/
structure NameConstraints where
  critical  : Option Bool
  permitted : List GeneralName
  excluded  : List GeneralName
  deriving Inhabited

/-- RFC 5280 §4.2.1.4 Certificate Policies. -/
structure CertificatePolicies where
  critical : Option Bool
  policies : List String
  deriving Repr, DecidableEq, Inhabited

/-- RFC 5280 §4.2.2.1 Authority Information Access (presence-only). -/
structure AuthorityInfoAccess where
  critical : Option Bool
  deriving Repr, DecidableEq, Inhabited

/-- Signature algorithm OID + raw DER bytes of the AlgorithmIdentifier. -/
structure SignatureAlgorithm where
  id    : String
  bytes : String
  deriving Repr, DecidableEq, Inhabited

/-- Generic extension record (OID + criticality) for extensions not
    specifically parsed. Used in `allExts` to check duplicates. -/
structure Extension where
  oid      : String
  critical : Option Bool
  deriving Repr, DecidableEq, Inhabited

/-! ## § 4  Abstract Certificate -/

/-- The abstract policy-layer certificate. Distinct from
    `Verdict.Certificate` (parser-layer / `SpecCertificateValue`).
    Mapping provided by `Verdict.certFromParsed` (see `Impl/Convert.lean`).

    Verus `rspec!` in `policy/common.rs`: `pub struct Certificate {...}`. -/
structure AbstractCertificate where
  fingerprint            : String
  version                : UInt32
  serial                 : String
  sigAlgOuter            : SignatureAlgorithm
  sigAlgInner            : SignatureAlgorithm
  notBefore              : UInt64
  notAfter               : UInt64
  issuer                 : DistinguishedName
  subject                : DistinguishedName
  subjectKey             : SubjectKey
  issuerUid              : Option String
  subjectUid             : Option String
  extAuthorityKeyId      : Option AuthorityKeyIdentifier
  extSubjectKeyId        : Option SubjectKeyIdentifier
  extExtendedKeyUsage    : Option ExtendedKeyUsage
  extBasicConstraints    : Option BasicConstraints
  extKeyUsage            : Option KeyUsage
  extSubjectAltName      : Option SubjectAltName
  extNameConstraints     : Option NameConstraints
  extCertPolicies        : Option CertificatePolicies
  extAuthorityInfoAccess : Option AuthorityInfoAccess
  allExts                : Option (List Extension)
  deriving Inhabited

/-! ## § 5  Task and Purpose -/

/-- Validation purpose. -/
inductive Purpose where
  | serverAuth
  deriving Repr, DecidableEq, Inhabited

/-- Policy-layer validation context. Distinct from `Verdict.Task` —
    that one carries fewer fields; this one matches Verus's internal
    `InternalTask` shape. -/
structure PolicyTask where
  hostname : Option String
  purpose  : Purpose
  now      : UInt64
  deriving Inhabited

/-- Policy execution error. -/
inductive PolicyError where
  | unsupportedTask
  deriving Repr

/-! ## § 6  String Normalization -/

/-- RFC 4518 string normalization for Distinguished Name comparison.
    Verus: `pub open spec fn spec_normalize_string(s: Seq<char>) -> Seq<char>`.
    Steps: (1) case-fold to lower; (2) strip leading/trailing spaces;
    (3) collapse internal space runs. -/
def normalizeString (s : String) : String :=
  s.toLower.splitOn " " |>.filter (!·.isEmpty) |> String.intercalate " "

/-! ## § 7  Predicate API -/

/-- Two attributes are equal with optional value normalization. -/
def sameAttr (a1 a2 : Attribute) (normalize : Bool) : Bool :=
  a1.oid == a2.oid &&
  if normalize then
    a1.value == a2.value || normalizeString a1.value == normalizeString a2.value
  else
    a1.value == a2.value

/-- RDN element-wise `sameAttr`. -/
def sameRDN (rdn1 rdn2 : List Attribute) (normalize : Bool) : Bool :=
  rdn1.length == rdn2.length &&
  (rdn1.zip rdn2).all fun (a1, a2) => sameAttr a1 a2 normalize

/-- DN-wise `sameRDN`. `normalize = true` → Chrome-style;
    `false` → Firefox-style exact. -/
def sameDN (dn1 dn2 : DistinguishedName) (normalize : Bool) : Bool :=
  dn1.rdns.length == dn2.rdns.length &&
  (dn1.rdns.zip dn2.rdns).all fun (r1, r2) => sameRDN r1 r2 normalize

/-- `name1` is a suffix-subset of `name2` at the RDN level. -/
def isSubtreeOf (name1 name2 : DistinguishedName) (normalize : Bool) : Bool :=
  name2.rdns.length ≤ name1.rdns.length &&
  sameDN { rdns := name1.rdns.drop (name1.rdns.length - name2.rdns.length) } name2 normalize

/-- RFC 6125 §6.4 wildcard hostname matching. Mirrors upstream Verus
    `match_name` (verdict/src/policy/common.rs): raw string comparison, no
    `normalizeString` — the wildcard suffix is checked against `name` verbatim,
    and the non-wildcard case is exact equality. -/
def matchName (pattern name : String) : Bool :=
  if pattern.startsWith "*." then
    let nameLen := name.length
    let patLen  := pattern.length
    patLen > 2 &&
      (String.ofList (pattern.toList.drop 2) == name ||
        (nameLen > patLen - 1 &&
         name.endsWith (String.ofList (pattern.toList.drop 1)) &&
         !(String.ofList (name.toList.take (nameLen - (patLen - 1)))).any (· == '.')))
  else
    pattern == name

/-- Name Constraints permitted-subtree check for a DNS name. Mirrors upstream
    Verus `permit_name` (verdict/src/policy/common.rs): raw comparison, no
    `normalizeString`. Empty constraint matches everything; a `.`-prefixed
    constraint must be a suffix of `name`; otherwise `name` equals the
    constraint or has a `.<constraint>` suffix. -/
def permitName (nameConstraint name : String) : Bool :=
  nameConstraint.isEmpty ||
  (if nameConstraint.startsWith "." then
    nameConstraint.length ≤ name.length &&
      String.ofList (name.toList.drop (name.length - nameConstraint.length)) == nameConstraint
  else
    name == nameConstraint ||
      (name.length > nameConstraint.length &&
       (name.toList.getD (name.length - nameConstraint.length - 1) ' ') == '.' &&
       String.ofList (name.toList.drop (name.length - nameConstraint.length)) == nameConstraint))

/-- IP-address subnet range check (IPv4: 8-byte range, 4-byte addr;
    IPv6: 32-byte range, 16-byte addr). -/
def ipAddrInRange (range addr : ByteArray) : Bool :=
  let addrLen := addr.size
  range.size == 2 * addrLen &&
  (List.range addrLen).all fun i =>
    (range[i]! &&& range[i + addrLen]!) == (addr[i]! &&& range[i + addrLen]!)

/-- RFC 5280 §4.2.1.1 Authority Key Identifier check. -/
def checkAuthKeyId (issuer subject : AbstractCertificate) : Bool :=
  match subject.extAuthorityKeyId with
  | none => true
  | some aki =>
    let keyIdOk := match (issuer.extSubjectKeyId, aki.keyId) with
      | (some skid, some akid) => skid.keyId == akid
      | _                      => true
    let serialOk := match aki.serial with
      | some s => s == issuer.serial
      | none   => true
    keyIdOk && serialOk

/-- No two extensions share the same OID. -/
def checkDuplicateExtensions (cert : AbstractCertificate) : Bool :=
  match cert.allExts with
  | none => true
  | some exts =>
    let oids := exts.map Extension.oid
    oids.eraseDups.length == oids.length

/-- Certificate has a DirectoryName in its Name Constraints. -/
def hasDirectoryNameConstraint (cert : AbstractCertificate) : Bool :=
  match cert.extNameConstraints with
  | none => false
  | some nc => nc.permitted.any fun gn => match gn with
    | .directoryName _ => true
    | _ => false

/-- Certificate has a DNSName in its Name Constraints. -/
def hasDnsNameConstraint (cert : AbstractCertificate) : Bool :=
  match cert.extNameConstraints with
  | none => false
  | some nc => nc.permitted.any fun gn => match gn with
    | .dnsName _ => true
    | _ => false

/-- Certificate has an IPAddr in its Name Constraints. -/
def hasIpAddrNameConstraint (cert : AbstractCertificate) : Bool :=
  match cert.extNameConstraints with
  | none => false
  | some nc => nc.permitted.any fun gn => match gn with
    | .ipAddr _ => true
    | _ => false

end Verdict.Policy

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- No benchmark APIs in this module — all content is curator-given
-- vocabulary consumed by the policy modules (Chrome / Firefox /
-- OpenSSL) and `Spec/Policy/Common.lean`.
