import Verdict.Impl.PolicyCommon

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Verdict.Impl.PolicyStandard

RFC 5280 conformance trait predicates. These are VOCABULARY
(`Prop`-valued predicates over a policy's `validChain` function),
not benchmark APIs — no markers, no `!benchmark code` blocks.

Each trait is parameterised by a `validChain : List AbstractCertificate →
PolicyTask → Bool` function and states a conformance property that
any sound chain-validation policy should satisfy. Instantiations for
the concrete Chrome / Firefox / OpenSSL policies live in
`Spec/PolicyStandard.lean`.

Upstream: `verdict/src/policy/standard.rs` — the Verus proof
conformance traits.
-/

namespace Verdict.Policy.Standard

open Verdict.Policy

/-! ## § 1  Time and Expiration -/

/-- All certificates in a valid chain have valid time bounds.
    RFC 5280 §4.1.2.5: `notBefore ≤ now ≤ notAfter`. -/
def TimeValidity (validChain : List AbstractCertificate → PolicyTask → Bool) : Prop :=
  ∀ chain task, validChain chain task = true →
    ∀ i, i < chain.length → chain[i]!.notBefore ≤ task.now ∧ task.now ≤ chain[i]!.notAfter

/-- Leaf certificate duration is bounded (policy-specific maximum lifetime). -/
def LeafDurationBound (validChain : List AbstractCertificate → PolicyTask → Bool)
    (maxDuration : UInt64) : Prop :=
  ∀ chain task, validChain chain task = true → chain.length ≥ 1 →
    let leaf := chain[0]!
    leaf.notAfter - leaf.notBefore ≤ maxDuration

/-! ## § 2  Signature Algorithm -/

/-- Inner and outer signature algorithm OIDs match on all certificates.
    RFC 5280 §4.1.1.2: `signatureAlgorithm` must match `signature` in TBSCertificate. -/
def SigAlgConsistency (validChain : List AbstractCertificate → PolicyTask → Bool) : Prop :=
  ∀ chain task, validChain chain task = true →
    ∀ i, i < chain.length → chain[i]!.sigAlgOuter.id = chain[i]!.sigAlgInner.id

/-- Non-root certificates use strong (≥ SHA-256) signature algorithms. -/
def StrongSignature (validChain : List AbstractCertificate → PolicyTask → Bool)
    (isStrong : String → Bool) : Prop :=
  ∀ chain task, validChain chain task = true →
    ∀ i, i + 1 < chain.length → isStrong chain[i]!.sigAlgOuter.id = true

/-! ## § 3  Basic Constraints and Path Length -/

/-- Non-leaf certificates have `isCA = true` in Basic Constraints.
    RFC 5280 §4.2.1.9. -/
def BasicConstraintsCA (validChain : List AbstractCertificate → PolicyTask → Bool) : Prop :=
  ∀ chain task, validChain chain task = true →
    ∀ i, 0 < i → i < chain.length →
      chain[i]!.extBasicConstraints.any (·.isCA) = true

/-- Path length constraints are respected: intermediate at depth `d`
    has `pathLen ≥ d` (when `pathLen` is present).
    RFC 5280 §4.2.1.9. -/
def PathLengthEnforced (validChain : List AbstractCertificate → PolicyTask → Bool) : Prop :=
  ∀ chain task, validChain chain task = true →
    ∀ i, 0 < i → i + 1 < chain.length →
      match chain[i]!.extBasicConstraints with
      | some bc => match bc.pathLen with
        | some pl => pl ≥ (i - 1 : Int)
        | none => True
      | none => True

/-! ## § 4  Key Usage -/

/-- CA certificates have `keyCertSign` set in Key Usage.
    RFC 5280 §4.2.1.3. -/
def KeyUsageCA (validChain : List AbstractCertificate → PolicyTask → Bool) : Prop :=
  ∀ chain task, validChain chain task = true →
    ∀ i, 0 < i → i < chain.length →
      match chain[i]!.extKeyUsage with
      | some ku => ku.keyCertSign = true
      | none => True

/-- Leaf certificate has appropriate key usage for TLS.
    RFC 5280 §4.2.1.3: `digitalSignature` or `keyEncipherment` or `keyAgreement`. -/
def KeyUsageLeaf (validChain : List AbstractCertificate → PolicyTask → Bool) : Prop :=
  ∀ chain task, validChain chain task = true → chain.length ≥ 1 →
    match chain[0]!.extKeyUsage with
    | some ku => ku.digitalSignature || ku.keyEncipherment || ku.keyAgreement
    | none => True

/-- Leaf certificate has `serverAuth` in Extended Key Usage.
    RFC 5280 §4.2.1.12. -/
def ExtendedKeyUsageLeaf (validChain : List AbstractCertificate → PolicyTask → Bool) : Prop :=
  ∀ chain task, validChain chain task = true → chain.length ≥ 1 →
    match chain[0]!.extExtendedKeyUsage with
    | some eku => eku.usages.any (· == .serverAuth) = true
    | none => True

/-! ## § 5  Extensions -/

/-- No certificate has duplicate extension OIDs.
    RFC 5280 §4.2. -/
def UniqueExtensions (validChain : List AbstractCertificate → PolicyTask → Bool) : Prop :=
  ∀ chain task, validChain chain task = true →
    ∀ i, i < chain.length → checkDuplicateExtensions chain[i]! = true

/-- Name constraints are respected across the chain.
    RFC 5280 §4.2.1.10. -/
def NameConstraintsRespected (validChain : List AbstractCertificate → PolicyTask → Bool)
    (checkNC : List AbstractCertificate → Bool) : Prop :=
  ∀ chain task, validChain chain task = true →
    checkNC chain = true

/-- AKI on subject matches issuer's SKI when both present.
    RFC 5280 §4.2.1.1. -/
def AuthorityKeyIdValid (validChain : List AbstractCertificate → PolicyTask → Bool) : Prop :=
  ∀ chain task, validChain chain task = true →
    ∀ i, i + 1 < chain.length →
      checkAuthKeyId chain[i + 1]! chain[i]! = true

/-! ## § 6  Key and PKI -/

/-- All certificates have valid PKI key types (policy-specific minimum). -/
def ValidPKI (validChain : List AbstractCertificate → PolicyTask → Bool)
    (isValidKey : AbstractCertificate → Bool) : Prop :=
  ∀ chain task, validChain chain task = true →
    ∀ i, i < chain.length → isValidKey chain[i]! = true

/-! ## § 7  Revocation -/

/-- No certificate in the chain is revoked (per CRL). -/
def NotRevoked (validChain : List AbstractCertificate → PolicyTask → Bool)
    (notInCrl : AbstractCertificate → Bool) : Prop :=
  ∀ chain task, validChain chain task = true →
    ∀ i, i < chain.length → notInCrl chain[i]! = true

/-! ## § 8  SAN and Hostname -/

/-- Leaf certificate SAN is present when hostname is specified. -/
def SubjectAltNamePresent (validChain : List AbstractCertificate → PolicyTask → Bool) : Prop :=
  ∀ chain task, validChain chain task = true → chain.length ≥ 1 →
    task.hostname.isSome →
      chain[0]!.extSubjectAltName.isSome = true

/-- Hostname matches leaf certificate SAN.
    RFC 6125 §6.4. -/
def HostnameMatch (validChain : List AbstractCertificate → PolicyTask → Bool)
    (checkHost : AbstractCertificate → String → Bool) : Prop :=
  ∀ chain task, validChain chain task = true → chain.length ≥ 1 →
    ∀ h, task.hostname = some h →
      checkHost chain[0]! h = true

/-! ## § 9  Chain Structure -/

/-- Valid chains have at least 2 certificates (leaf + root).
    Verus: `chain.len() >= 2` in all `valid_chain` implementations. -/
def ChainMinLength (validChain : List AbstractCertificate → PolicyTask → Bool) : Prop :=
  ∀ chain task, validChain chain task = true → chain.length ≥ 2

/-- Certificate version is v3 (2) for certificates with extensions.
    RFC 5280 §4.1.2.1. -/
def ValidVersion (validChain : List AbstractCertificate → PolicyTask → Bool) : Prop :=
  ∀ chain task, validChain chain task = true →
    ∀ i, i < chain.length →
      chain[i]!.allExts.isSome → chain[i]!.version ≥ 3

end Verdict.Policy.Standard
