import Verdict.Harness

/-!
# Verdict.Test

Executable conformance tests. `#guard` assertions exercise the
curator's reference implementations.

DO NOT MODIFY — infrastructure.
-/

-- ── charToBits ────────────────────────────────────────────────
#guard Verdict.charToBits 0x41 = some (some 0)   -- 'A'
#guard Verdict.charToBits 0x5A = some (some 25)  -- 'Z'
#guard Verdict.charToBits 0x61 = some (some 26)  -- 'a'
#guard Verdict.charToBits 0x30 = some (some 52)  -- '0'
#guard Verdict.charToBits 0x39 = some (some 61)  -- '9'
#guard Verdict.charToBits 0x2B = some (some 62)  -- '+'
#guard Verdict.charToBits 0x2F = some (some 63)  -- '/'
#guard Verdict.charToBits 0x3D = some none       -- '='
#guard Verdict.charToBits 0x20 = none            -- ' '

-- ── decode6Bits (bit layout) ──────────────────────────────────
#guard Verdict.decode6Bits 0 0 0 0 = [0x00, 0x00, 0x00]
-- All-high 6-bit values: each output byte is 0xFF.
#guard Verdict.decode6Bits 63 63 63 63 = [0xFF, 0xFF, 0xFF]
-- First input shifts into byte 0 top bits.
#guard Verdict.decode6Bits 63 0 0 0 = [0xFC, 0x00, 0x00]
-- Last input lands in byte 2 low bits.
#guard Verdict.decode6Bits 0 0 0 63 = [0x00, 0x00, 0x3F]

-- ── decodeBase64 round-trip on a 4-char block ────────────────
-- "TWFu" = b"Man" in base64
#guard Verdict.decodeBase64 [0x54, 0x57, 0x46, 0x75] = some [0x4D, 0x61, 0x6E]
-- Empty input decodes to empty output.
#guard Verdict.decodeBase64 [] = some []
-- Odd length (not a multiple of 4) is rejected.
#guard Verdict.decodeBase64 [0x54] = none
#guard Verdict.decodeBase64 [0x54, 0x57, 0x46] = none
-- Padding `=` is NOT supported by the reference impl (see docstring).
-- Any `=` in a 4-char block falls through to `none`.
#guard Verdict.decodeBase64 [0x54, 0x57, 0x46, 0x3D] = none
-- Invalid characters (e.g. space) are rejected.
#guard Verdict.decodeBase64 [0x20, 0x57, 0x46, 0x75] = none

-- ── normalizeString (empty-only; `charLower` is opaque so any
--    non-empty input is not `decide`-reducible) ───────────────
#guard Verdict.normalizeString "" = ""

-- ── isSimplePath ──────────────────────────────────────────────
#guard Verdict.isSimplePath [] = true
#guard Verdict.isSimplePath [0] = true
#guard Verdict.isSimplePath [0, 1, 2] = true
#guard Verdict.isSimplePath [0, 1, 0] = false

-- ── pathInBounds ──────────────────────────────────────────────
#guard Verdict.pathInBounds [0, 1, 2] 3 = true
#guard Verdict.pathInBounds [0, 1, 3] 3 = false
#guard Verdict.pathInBounds [] 0 = true

-- ── chainFromPath ─────────────────────────────────────────────
#guard (Verdict.chainFromPath ([] : List Verdict.Certificate) [] default).length = 1
#guard (Verdict.chainFromPath
    ([default, default] : List Verdict.Certificate)
    [0, 1] default).length = 3

-- ── validateX509Base64 short-circuits on empty bundle ────────
#guard (Verdict.validateX509Base64 [] [] ⟨none, 0⟩).isOk = false

-- Reference policy cases use the pinned source's time, CA and name rules.
private def policyDn : Verdict.Policy.DistinguishedName :=
  ⟨[[⟨"2.5.4.3", "example.test"⟩]]⟩

private def policyLeaf : Verdict.Policy.AbstractCertificate :=
  { (default : Verdict.Policy.AbstractCertificate) with
    version := 2
    sigAlgOuter := ⟨"1.2.840.113549.1.1.11", "algorithm"⟩
    sigAlgInner := ⟨"1.2.840.113549.1.1.11", "algorithm"⟩
    notBefore := 0
    notAfter := 10
    issuer := policyDn
    subject := policyDn
    subjectKey := .rsa 2048
    extAuthorityKeyId := some ⟨none, some "key", none, none⟩ }

private def policyRoot : Verdict.Policy.AbstractCertificate :=
  { policyLeaf with
    extBasicConstraints := some ⟨some true, true, none⟩
    extKeyUsage := some { (default : Verdict.Policy.KeyUsage) with keyCertSign := true }
    extSubjectKeyId := some ⟨none, "key"⟩ }

private def policyTask : Verdict.Policy.PolicyTask := ⟨none, .serverAuth, 1⟩

#guard Verdict.toHexUpper [0, 15, 16, 171, 255] == "000F10ABFF"
#guard Verdict.chromeValidChain default [policyLeaf, policyRoot] policyTask
#guard Verdict.firefoxValidChain default [policyLeaf, policyRoot] policyTask
#guard Verdict.opensslValidChain [policyLeaf, policyRoot] policyTask
#guard !Verdict.chromeValidChain default [] policyTask
#guard !Verdict.firefoxValidChain default [policyLeaf] policyTask
#guard !Verdict.opensslValidChain [policyLeaf] policyTask
#guard !Verdict.chromeCertVerifiedLeaf default policyTask { policyLeaf with notAfter := 0 } policyRoot
#guard !Verdict.firefoxCertVerifiedLeaf default policyTask { policyLeaf with subjectKey := .rsa 1024 } false
#guard !Verdict.opensslValidLeaf { policyTask with now := 10 } policyLeaf
#guard Verdict.chromeLikelyIssued policyRoot policyLeaf
#guard Verdict.firefoxLikelyIssued policyRoot policyLeaf
#guard Verdict.opensslLikelyIssued policyRoot policyLeaf
#guard !Verdict.firefoxLikelyIssued policyRoot
  { policyLeaf with extAuthorityKeyId := some ⟨none, some "wrong-key", none, none⟩ }
#guard !Verdict.opensslCheckHostname
  { policyLeaf with extSubjectAltName := some ⟨none, [.dnsName "other.test"]⟩ } "example.test"
#guard !Verdict.firefoxCheckAllNameConstraints
  [policyLeaf, { policyRoot with extNameConstraints := some ⟨none, [], [.dnsName "example.test"]⟩ }]
