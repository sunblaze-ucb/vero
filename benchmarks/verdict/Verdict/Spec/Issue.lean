import Verdict.Harness

/-!
# Verdict.Spec.Issue

Specifications for `normalizeString` and `verifySignature`.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- Normalizing a string doesn't make it longer — the only operations
    are lowercase fold (which can expand under full Unicode but stays
    within ASCII bounds for ASCII input) and whitespace collapse. For
    ASCII-only inputs the length is preserved or shrinks. -/
def spec_normalize_ascii_length_bound (impl : RepoImpl) : Prop :=
  ∀ (s : String),
    (∀ c, c ∈ s.toList → c.val ≥ 0x20 ∧ c.val ≤ 0x7E) →
    (impl.verdict.normalizeString s).length ≤ s.length

/-- Normalized strings have no leading space. -/
def spec_normalize_no_leading_space (impl : RepoImpl) : Prop :=
  ∀ (s : String),
    let ns := impl.verdict.normalizeString s
    (ns.toList).head? ≠ some ' '

/-- Normalized ASCII strings have no trailing space. -/
def spec_normalize_no_trailing_space (impl : RepoImpl) : Prop :=
  ∀ (s : String),
    (∀ c, c ∈ s.toList → c.val ≥ 0x20 ∧ c.val ≤ 0x7E) →
    let ns := impl.verdict.normalizeString s
    (ns.toList).getLast? ≠ some ' '

/-- Empty input yields empty output. -/
def spec_normalize_empty (impl : RepoImpl) : Prop :=
  impl.verdict.normalizeString "" = ""

/-- `normalizeString` is idempotent: a second pass doesn't shrink or
    grow a string that's already normalized. Not a named Verus lemma,
    but a natural consequence of the three-phase pipeline (the first
    pass case-folds + trims + collapses; a second pass finds nothing
    left to change). -/
def spec_normalize_idempotent (impl : RepoImpl) : Prop :=
  ∀ (s : String),
    impl.verdict.normalizeString (impl.verdict.normalizeString s)
      = impl.verdict.normalizeString s

/-- `issuedByRaw` requires `verifySignature` to succeed. -/
def spec_issued_by_raw_needs_signature (impl : RepoImpl) : Prop :=
  ∀ (issuer subject : Verdict.Certificate),
    impl.verdict.issuedByRaw issuer subject = true →
    impl.verdict.verifySignature issuer subject = true

/-- `issuedByRaw` requires the subject/issuer names to match. -/
def spec_issued_by_raw_names_match (impl : RepoImpl) : Prop :=
  ∀ (issuer subject : Verdict.Certificate),
    impl.verdict.issuedByRaw issuer subject = true →
    issuer.cert.subject = subject.cert.issuer
