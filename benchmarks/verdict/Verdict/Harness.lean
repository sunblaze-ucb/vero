import Verdict.Bundle

/-!
# Verdict.Harness

Benchmark harness: `RepoImpl` (one field per package), `canonical`
wiring to the `Impl/` stubs, and the standard `joint_unsat` macro.

DO NOT MODIFY — benchmark infrastructure.
-/

-- ── Implementation bundle ────────────────────────────────────

structure RepoImpl where
  verdict : VerdictBundle

-- ── Canonical instance ───────────────────────────────────────

def canonical : RepoImpl where
  verdict := {
    charToBits          := Verdict.charToBits
    decode6Bits         := Verdict.decode6Bits
    decodeBase64        := Verdict.decodeBase64
    parseX509Base64     := Verdict.parseX509Base64
    normalizeString     := Verdict.normalizeString
    verifySignature     := Verdict.verifySignature
    issuedByRaw         := Verdict.issuedByRaw
    isSimplePath        := Verdict.isSimplePath
    pathInBounds        := Verdict.pathInBounds
    chainFromPath       := Verdict.chainFromPath
    validateX509Base64  := Verdict.validateX509Base64
    chromeCertVerifiedLeaf         := Verdict.chromeCertVerifiedLeaf
    chromeCertVerifiedIntermediate := Verdict.chromeCertVerifiedIntermediate
    chromeCertVerifiedRoot         := Verdict.chromeCertVerifiedRoot
    chromeCheckAllNameConstraints  := Verdict.chromeCheckAllNameConstraints
    chromeLikelyIssued             := Verdict.chromeLikelyIssued
    chromeValidChain               := Verdict.chromeValidChain
    firefoxCertVerifiedLeaf         := Verdict.firefoxCertVerifiedLeaf
    firefoxCertVerifiedIntermediate := Verdict.firefoxCertVerifiedIntermediate
    firefoxCertVerifiedRoot         := Verdict.firefoxCertVerifiedRoot
    firefoxCheckAllNameConstraints  := Verdict.firefoxCheckAllNameConstraints
    firefoxLikelyIssued             := Verdict.firefoxLikelyIssued
    firefoxValidChain               := Verdict.firefoxValidChain
    opensslValidLeaf             := Verdict.opensslValidLeaf
    opensslValidIntermediate     := Verdict.opensslValidIntermediate
    opensslValidRoot             := Verdict.opensslValidRoot
    opensslCheckNameConstraints  := Verdict.opensslCheckNameConstraints
    opensslCheckHostname         := Verdict.opensslCheckHostname
    opensslLikelyIssued          := Verdict.opensslLikelyIssued
    opensslValidChain            := Verdict.opensslValidChain
    toHexUpper     := Verdict.toHexUpper
  }

-- ── joint_unsat macro ────────────────────────────────────────

syntax "joint_unsat" ident ident ident* "by" tacticSeq : command

open Lean in
macro_rules
  | `(joint_unsat $s1 $s2 $[$rest]* by $proof) => do
    let specs := #[s1, s2] ++ rest
    let name := specs.foldl (init := `joint_unsat) fun acc s => Name.append acc s.getId
    let mut body ← `($(specs[0]!) impl)
    for s in specs[1:] do
      body ← `($body ∧ $s impl)
    `(theorem $(mkIdent name) : ¬ ∃ impl : RepoImpl, $body := by $proof)
