import Verdict.Harness

/-!
# Verdict.Spec.PolicyCommon

Specifications for `Verdict.Policy.*` helpers. Each `spec_*` takes an
arbitrary `impl : RepoImpl`. (Most of these helpers are curator-given
vocabulary — so the specs are properties of the fixed implementations
rather than obligations on `impl`-level APIs. `impl` is kept in the
signature for uniformity with the rest of the Spec layer.)

DO NOT MODIFY — this file is frozen curator-given content.

Upstream: `verdict/src/policy/common.rs` (ported 2026-04-21 from
`verdict_old/Verdict/Spec/Policy/Common.lean`).
-/

open Verdict.Policy

/-! ## § 1  String Normalization in DN Comparison -/

/-- `sameAttr` with `normalize = true` uses `normalizeString` for value
    comparison. Verus: `same_attr` body. -/
def spec_same_attr_normalize (_impl : RepoImpl) : Prop :=
  ∀ (a1 a2 : Verdict.Policy.Attribute),
    Verdict.Policy.sameAttr a1 a2 true = true →
    (a1.oid = a2.oid ∧
     (a1.value = a2.value ∨
      Verdict.Policy.normalizeString a1.value
        = Verdict.Policy.normalizeString a2.value))

/-- `sameAttr` without normalization is exact string equality. -/
def spec_same_attr_exact (_impl : RepoImpl) : Prop :=
  ∀ (a1 a2 : Verdict.Policy.Attribute),
    Verdict.Policy.sameAttr a1 a2 false = true ↔
      a1.oid = a2.oid ∧ a1.value = a2.value

/-! ## § 2  Distinguished Name Equality -/

/-- `sameDN` is reflexive. -/
def spec_same_dn_refl (_impl : RepoImpl) : Prop :=
  ∀ (dn : Verdict.Policy.DistinguishedName) (norm : Bool),
    Verdict.Policy.sameDN dn dn norm = true

/-- `sameDN` is symmetric. -/
def spec_same_dn_symm (_impl : RepoImpl) : Prop :=
  ∀ (dn1 dn2 : Verdict.Policy.DistinguishedName) (norm : Bool),
    Verdict.Policy.sameDN dn1 dn2 norm = Verdict.Policy.sameDN dn2 dn1 norm

/-- `sameDN` is transitive. -/
def spec_same_dn_trans (_impl : RepoImpl) : Prop :=
  ∀ (dn1 dn2 dn3 : Verdict.Policy.DistinguishedName) (norm : Bool),
    Verdict.Policy.sameDN dn1 dn2 norm = true →
    Verdict.Policy.sameDN dn2 dn3 norm = true →
    Verdict.Policy.sameDN dn1 dn3 norm = true

/-- Strict equality implies normalized equality. -/
def spec_same_dn_strict_implies_normalized (_impl : RepoImpl) : Prop :=
  ∀ (dn1 dn2 : Verdict.Policy.DistinguishedName),
    Verdict.Policy.sameDN dn1 dn2 false = true →
    Verdict.Policy.sameDN dn1 dn2 true = true

/-- DNs with different RDN counts are never equal. -/
def spec_same_dn_length_mismatch (_impl : RepoImpl) : Prop :=
  ∀ (dn1 dn2 : Verdict.Policy.DistinguishedName) (norm : Bool),
    dn1.rdns.length ≠ dn2.rdns.length →
    Verdict.Policy.sameDN dn1 dn2 norm = false

/-- `sameDN` decomposes into per-RDN `sameRDN` checks. -/
def spec_same_dn_iff_same_rdn (_impl : RepoImpl) : Prop :=
  ∀ (dn1 dn2 : Verdict.Policy.DistinguishedName) (norm : Bool),
    Verdict.Policy.sameDN dn1 dn2 norm = true ↔
      dn1.rdns.length = dn2.rdns.length ∧
      ∀ i, (hi : i < dn1.rdns.length) →
        Verdict.Policy.sameRDN dn1.rdns[i]! dn2.rdns[i]! norm = true

/-! ## § 3  Hostname Matching -/

/-- Non-wildcard patterns reject different strings. -/
def spec_match_name_exact_only (_impl : RepoImpl) : Prop :=
  ∀ (pattern name : String),
    pattern ≠ name →
    ¬ pattern.startsWith "*." →
    Verdict.Policy.matchName pattern name = false

/-- Wildcard `*.d` matches the base domain `d` (for a nonempty domain `d`;
    the bare pattern `"*."` has no domain and matches nothing). -/
def spec_match_name_wildcard_base (_impl : RepoImpl) : Prop :=
  ∀ (d : String), d ≠ "" → Verdict.Policy.matchName ("*." ++ d) d = true

/-- Wildcard `*.d` matches `x.d` (`d` and `x` nonempty, `x` has no `.`). -/
def spec_match_name_wildcard_single_label (_impl : RepoImpl) : Prop :=
  ∀ (d x : String),
    d ≠ "" →
    x ≠ "" →
    ¬ x.any (· == '.') →
    Verdict.Policy.matchName ("*." ++ d) (x ++ "." ++ d) = true

/-- Wildcard `*.d` rejects multi-label names `x.y.d`. -/
def spec_match_name_wildcard_multi_label_rejected (_impl : RepoImpl) : Prop :=
  ∀ (d x y : String),
    x ≠ "" → y ≠ "" →
    ¬ x.any (· == '.') → ¬ y.any (· == '.') →
    Verdict.Policy.matchName ("*." ++ d) (x ++ "." ++ y ++ "." ++ d) = false

/-! ## § 4  Name Constraints -/

/-- Empty constraint permits any name. -/
def spec_permit_name_empty_constraint (_impl : RepoImpl) : Prop :=
  ∀ (name : String), Verdict.Policy.permitName "" name = true

/-- A constraint `".suffix"` permits exactly the names that end with the full
    dotted constraint `".suffix"`. -/
def spec_permit_name_dot_prefix (_impl : RepoImpl) : Prop :=
  ∀ (suffix name : String),
    name.endsWith ("." ++ suffix) →
    Verdict.Policy.permitName ("." ++ suffix) name = true

/-- IPv4 range check unfolds to a bitwise-AND per byte. -/
def spec_ip_addr_in_range_ipv4 (_impl : RepoImpl) : Prop :=
  ∀ (range addr : ByteArray),
    range.size = 8 → addr.size = 4 →
    (Verdict.Policy.ipAddrInRange range addr = true ↔
     ∀ i : Nat, i < 4 →
       (range[i]! &&& range[i + 4]!) = (addr[i]! &&& range[i + 4]!))

/-! ## § 5  Authority Key Identifier -/

/-- No AKI on subject ⇒ check passes. -/
def spec_check_auth_key_id_no_aki (_impl : RepoImpl) : Prop :=
  ∀ (issuer subject : Verdict.Policy.AbstractCertificate),
    subject.extAuthorityKeyId = none →
    Verdict.Policy.checkAuthKeyId issuer subject = true

/-- Matching key IDs (serial absent) ⇒ check passes. -/
def spec_check_auth_key_id_match (_impl : RepoImpl) : Prop :=
  ∀ (issuer subject : Verdict.Policy.AbstractCertificate) (kid : String),
    issuer.extSubjectKeyId = some { critical := none, keyId := kid } →
    subject.extAuthorityKeyId =
      some { critical := none, keyId := some kid, issuer := none, serial := none } →
    Verdict.Policy.checkAuthKeyId issuer subject = true

/-- Mismatched key IDs ⇒ check fails. -/
def spec_check_auth_key_id_mismatch (_impl : RepoImpl) : Prop :=
  ∀ (issuer subject : Verdict.Policy.AbstractCertificate) (k1 k2 : String),
    k1 ≠ k2 →
    issuer.extSubjectKeyId = some { critical := none, keyId := k1 } →
    subject.extAuthorityKeyId =
      some { critical := none, keyId := some k2, issuer := none, serial := none } →
    Verdict.Policy.checkAuthKeyId issuer subject = false

/-! ## § 6  Duplicate Extensions -/

/-- `none` `allExts` ⇒ no duplicate OIDs (trivially). -/
def spec_check_duplicate_extensions_none (_impl : RepoImpl) : Prop :=
  ∀ (cert : Verdict.Policy.AbstractCertificate),
    cert.allExts = none →
    Verdict.Policy.checkDuplicateExtensions cert = true
