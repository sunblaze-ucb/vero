import Verdict.Impl.Base64

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Verdict.Impl.Issue

String normalization and certificate signature verification. Both
are `pub fn` in Verus with companion `spec fn`s; in Lean we model
them as `!benchmark code` tasks (for `normalizeString`) and as a
dispatching stub that calls the opaque crypto primitives (for
`verifySignature`).

Upstream: `verdict/src/issue.rs`.
-/

namespace Verdict

-- ── API signatures (DO NOT MODIFY) ───────────────────────────

/-- Normalize a string per a subset of RFC 4518: lowercase, trim
    leading/trailing ASCII spaces, collapse internal runs of ASCII
    space into a single space. Non-ASCII is case-folded via
    `charLower`. -/
abbrev NormalizeStringSig := String → String

/-- Verify that `subject`'s outer signature is valid under `issuer`'s
    public key, according to RFC 5280. Dispatches by algorithm OID
    on `issuer.cert.subjectKey.alg` and `subject.sigAlg`. -/
abbrev VerifySignatureSig := Certificate → Certificate → Bool

/-- `issuedByRaw policy issuer subject` checks the policy's
    `likelyIssued` predicate conjoined with `verifySignature`.
    Encoded here as a bare `verifySignature` since the policy layer is
    abstracted away in this benchmark. -/
abbrev IssuedByRawSig := Certificate → Certificate → Bool

end Verdict

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- ── Implementations ──────────────────────────────────────────

-- !benchmark @start code_aux def=normalizeString
-- !benchmark @end code_aux def=normalizeString

/-- Three-pass implementation: (1) split into characters,
    (2) lowercase each via `charLower`, (3) walk the result trimming
    leading / trailing spaces and collapsing internal runs. -/
def Verdict.normalizeString : Verdict.NormalizeStringSig :=
-- !benchmark @start code def=normalizeString
  fun s =>
    let chars := (s.toList.flatMap Verdict.charLower)
    let rec go : Bool → Bool → List Char → List Char
      | _,       _,       []     => []
      | seenNw,  seenWs,  c :: cs =>
        if c = ' ' then
          go seenNw true cs
        else if seenNw ∧ seenWs then
          ' ' :: c :: go true false cs
        else
          c :: go true false cs
    String.ofList (go false false chars)
-- !benchmark @end code def=normalizeString

-- !benchmark @start code_aux def=verifySignature
-- !benchmark @end code_aux def=verifySignature

/-- Dispatches to the opaque primitive matching issuer's key type +
    subject's signature algorithm. Returns `false` if no supported
    scheme applies. -/
def Verdict.verifySignature : Verdict.VerifySignatureSig :=
-- !benchmark @start code def=verifySignature
  fun issuer subject =>
    let alg := issuer.cert.subjectKey.alg
    let sigAlg := subject.sigAlg
    let tbs := subject.cert.serialized
    let sig := subject.sig.bytes
    -- We use the OID oid-bytes directly to dispatch. In production
    -- the OIDs are fixed constants; here we treat any RSA algorithm
    -- parameter as "load as RSA key", and fall through to the EC
    -- curves by serialized params content.
    match Verdict.pkcs1V15LoadPubKey alg.oid with
    | some pk => Verdict.pkcs1V15Verify sigAlg pk sig tbs
    | none    =>
      -- Fallback: try ECDSA
      Verdict.p256Verify sigAlg alg.oid sig tbs ||
      Verdict.p384Verify sigAlg alg.oid sig tbs
-- !benchmark @end code def=verifySignature

-- !benchmark @start code_aux def=issuedByRaw
-- !benchmark @end code_aux def=issuedByRaw

/-- Combine the policy's "likely issuer" check (here simplified to
    "same issuer / subject bytes") with actual signature verification. -/
def Verdict.issuedByRaw : Verdict.IssuedByRawSig :=
-- !benchmark @start code def=issuedByRaw
  fun issuer subject =>
    decide (issuer.cert.subject = subject.cert.issuer) &&
    Verdict.verifySignature issuer subject
-- !benchmark @end code def=issuedByRaw
