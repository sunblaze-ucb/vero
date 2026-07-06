import Verdict.Harness
import Verdict.Impl.Convert

/-!
# Verdict.Spec.Convert

Preservation specifications for `Verdict.certFromParsed`.

These mirror the three Verus-proved preservation facts on
`Certificate::spec_from` (`verdict/src/convert.rs`): the outer and
inner signature-algorithm OIDs survive the parser→policy translation
unchanged, and the validity bounds map over directly.

`certFromParsed` is `opaque` at the Impl layer (full conversion is
~1125 Rust LOC), so we reference it directly as
`Verdict.certFromParsed` rather than through `impl.verdict.*`; the
`impl` parameter is therefore ignored (`_impl`).

Note on types: the parser-layer `AlgorithmId.oid` is `Bytes`
(`List UInt8`, the raw OID DER-encoded bytes) whereas the
policy-layer `SignatureAlgorithm.id` is `String`. In Verus both
sides are `SpecString`, so the preservation fact is stated as
identity. In Lean we express the byte-to-string correspondence via
the standard `String.mk ∘ map (Char.ofNat ∘ UInt8.toNat)` encoding;
a concrete implementation must agree on the same encoding.

DO NOT MODIFY — curator-given spec.
-/

/-- Byte → char encoding used to compare a parser-layer OID (`Bytes`)
    against a policy-layer OID (`String`). -/
private def bytesToString (bs : Verdict.Bytes) : String :=
  String.ofList (bs.map (Char.ofNat ∘ UInt8.toNat))

/-- `certFromParsed` preserves the outer signature-algorithm OID.
    Verus: `Certificate::spec_from` (convert.rs) — outer `sigAlg`
    OID maps identity. -/
def spec_cert_from_parsed_sig_alg_outer (_impl : RepoImpl) : Prop :=
  ∀ (raw : Verdict.Certificate) (cert : Verdict.Policy.AbstractCertificate),
    Verdict.certFromParsed raw = some cert →
    cert.sigAlgOuter.id = bytesToString raw.sigAlg.oid

/-- `certFromParsed` preserves the inner (TBS) signature-algorithm
    OID. Verus: `Certificate::spec_from` — `sigAlgInner` of the
    policy cert equals the OID of the TBS `signature` field in the
    raw parse. -/
def spec_cert_from_parsed_sig_alg_inner (_impl : RepoImpl) : Prop :=
  ∀ (raw : Verdict.Certificate) (cert : Verdict.Policy.AbstractCertificate),
    Verdict.certFromParsed raw = some cert →
    cert.sigAlgInner.id = bytesToString raw.cert.sigAlg.oid

/-- `certFromParsed` preserves the validity bounds.
    The raw parsed validity carries `Bytes` for `notBefore` /
    `notAfter` (a UTCTime or GeneralizedTime byte string); the
    policy layer carries `UInt64` epoch seconds. We state the
    relationship via an existential time-decoder, since there is no
    concrete curator decoder exposed — every legitimate
    implementation must pick one and then the relation holds with
    the chosen decoder. -/
def spec_cert_from_parsed_validity (_impl : RepoImpl) : Prop :=
  ∃ (decode : Verdict.Bytes → UInt64),
    ∀ (raw : Verdict.Certificate) (cert : Verdict.Policy.AbstractCertificate),
      Verdict.certFromParsed raw = some cert →
      cert.notBefore = decode raw.cert.validity.notBefore ∧
      cert.notAfter  = decode raw.cert.validity.notAfter
