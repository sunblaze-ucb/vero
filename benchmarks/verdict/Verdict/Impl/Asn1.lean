import Verdict.Impl.Crypto

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Verdict.Impl.Asn1

Abstract X.509 certificate representation plus the opaque DER parser.
Parsing is delegated to an external vest-combinator stack in Verus;
here we model it as `opaque`. This means `parseX509Der` is NOT a
benchmark task — the LLM will never be asked to implement it.

Curator-declared axioms give the three facts we need about the
parser: it's deterministic, it rejects the empty input, and parsed
certificates carry a well-defined TBS blob.

Upstream:
- `verdict-parser/src/x509/`
- `verdict-parser/src/common/{bitstring.rs,octet.rs,oid.rs}`
-/

namespace Verdict

/-! ## § 1  Abstract data types -/

/-- A bit-string value with a byte payload + padding bits (the ASN.1
    notion). -/
structure BitString where
  bytes : Bytes
  unusedBits : Nat
  deriving DecidableEq, Inhabited

/-- Subject public key info: the algorithm identifier plus the
    opaque key blob. -/
structure SubjectPublicKeyInfo where
  alg : AlgorithmId
  pubKey : BitString
  deriving Inhabited

/-- A validity period: two `BytesString` dates (UTCTime or
    GeneralizedTime, not distinguished here). -/
structure Validity where
  notBefore : Bytes
  notAfter  : Bytes
  deriving Inhabited

/-- Abstract parsed TBS ("to-be-signed") certificate fields.

    Verus: `SpecTBSCertificate`. Kept minimal — only the fields
    downstream specs refer to. -/
structure TbsCertificate where
  serialized  : Bytes
  serial      : Bytes
  issuer      : Bytes
  subject     : Bytes
  validity    : Validity
  subjectKey  : SubjectPublicKeyInfo
  sigAlg      : AlgorithmId
  deriving Inhabited

/-- Abstract parsed certificate: TBS + outer signature algorithm +
    outer signature.

    Verus: `SpecCertificateValue`. Only the fields used by downstream
    specs are retained. -/
structure Certificate where
  cert    : TbsCertificate
  sigAlg  : AlgorithmId
  sig     : BitString
  deriving Inhabited

end Verdict

-- !benchmark @start global_aux
-- !benchmark @end global_aux

/-! ## § 2  Opaque parser -/

namespace Verdict

/-- Parse a DER-encoded X.509 certificate. Upstream:
    `verdict-parser/src/lib.rs:13` (`pub closed spec fn
    spec_parse_x509_der`) + the exec wrapper at line 43 which
    couples to the spec via `ensures`. `opaque` here because the
    full DER grammar is 2k+ lines of vest combinators in Verus —
    not a meaningful Lean benchmark task. Returns `none` on
    malformed input.

    No free-floating axioms are declared. The Verus `ensures` block
    (`verdict-parser/src/lib.rs:43-79`) characterises the exec fn's
    behaviour, not the opaque spec. If a future Lean spec requires
    one of those properties (e.g., suffix-non-malleability), it
    would be added here as a single named axiom. -/
opaque parseX509Der : Bytes → Option Certificate

end Verdict
