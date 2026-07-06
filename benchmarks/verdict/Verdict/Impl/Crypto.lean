-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Verdict.Impl.Crypto

Trusted cryptographic primitives. Each primitive corresponds to an
upstream Verus `pub uninterp spec fn` (which exec wrappers couple to
via `ensures res@ == spec_foo(...)`). In Lean we model them as
`opaque` declarations — they are *not* benchmark tasks and the LLM
must NOT attempt to implement them.

No free-floating axioms are declared here. The upstream Verus pattern
is `uninterp spec fn` + `ensures` coupling on the exec fn — Verus
does not state facts about the spec itself, and neither do we. If a
future Lean spec genuinely requires an algebraic property (e.g., a
suffix-non-malleability fact about `parseX509Der` mirroring
`verdict-parser/src/lib.rs:52-78`), it would be added then as a
single named axiom + a matching entry in
`manifest.json::trusted_axioms`.

Upstream:
- `verdict/src/hash.rs`             (`spec_sha256_digest`)
- `verdict/src/signature/rsa_*.rs`  (PKCS#1 v1.5 load/verify)
- `verdict/src/signature/ecdsa_*.rs` (P-256 / P-384 verify)
- `verdict/src/issue.rs:167`        (`spec_char_lower`)
-/

namespace Verdict

/-! ## § 1  Abstract types

These stand in for the external opaque types used by the verifier. -/

/-- A byte string, the common payload type for all crypto primitives.
    Modeled as `List UInt8` (not `ByteArray`) so specs can pattern
    match easily. -/
abbrev Bytes := List UInt8

/-- Abstract X.509 algorithm identifier (OID + params, decoded from
    DER). In Verus: `SpecAlgorithmIdentifier`. Body withheld; callers
    treat it as opaque and compare them via `=`. -/
structure AlgorithmId where
  oid : Bytes
  /-- Serialized params blob. Empty when the algorithm has no
      parameters. -/
  params : Bytes
  deriving DecidableEq, Inhabited

/-- Abstract RSA public key as loaded by AWS-LC / libcrux. The
    internal layout is opaque; the verifier only ever passes it
    between `pkcs1V15LoadPubKey` and `pkcs1V15Verify`. Inhabitation
    is not required: no structure carries `RsaPublicKey` as a field,
    and `Option RsaPublicKey` (the return type of
    `pkcs1V15LoadPubKey`) is `Inhabited` via `none`. -/
opaque RsaPublicKey : Type

end Verdict

-- !benchmark @start global_aux
-- !benchmark @end global_aux

/-! ## § 2  Opaque primitives -/

namespace Verdict

/-- Load an RSA public key from raw `SubjectPublicKeyInfo` bytes.
    External: AWS-LC / libcrux. `none` iff the key blob is malformed. -/
opaque pkcs1V15LoadPubKey : Bytes → Option RsaPublicKey

/-- RSA PKCS#1 v1.5 signature verification.
    External: AWS-LC / libcrux. -/
opaque pkcs1V15Verify : AlgorithmId → RsaPublicKey → Bytes → Bytes → Bool

/-- ECDSA P-256 verification. External: libcrux. -/
opaque p256Verify : AlgorithmId → Bytes → Bytes → Bytes → Bool

/-- ECDSA P-384 verification. External: AWS-LC. -/
opaque p384Verify : AlgorithmId → Bytes → Bytes → Bytes → Bool

/-- SHA-256 digest. External: AWS-LC. -/
opaque sha256Digest : Bytes → Bytes

/-- `char::to_lowercase` from Rust's stdlib. Returns a list of chars
    (Unicode case folding can expand a single char to several). -/
opaque charLower : Char → List Char

end Verdict
