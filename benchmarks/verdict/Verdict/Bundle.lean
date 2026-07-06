import Verdict.Impl.Crypto
import Verdict.Impl.Asn1
import Verdict.Impl.Base64
import Verdict.Impl.Issue
import Verdict.Impl.Validator
import Verdict.Impl.PolicyCommon
import Verdict.Impl.PolicyChrome
import Verdict.Impl.PolicyFirefox
import Verdict.Impl.PolicyOpenSSL
import Verdict.Impl.PolicyStandard
import Verdict.Impl.Convert
import Verdict.Impl.Hex

/-!
# Verdict.Bundle

Per-package implementation bundle for the `Verdict` root package.
Collects all API signatures into one structure. The opaque crypto
primitives live in `Impl/Crypto.lean`; they are NOT bundled here
because they are not benchmark tasks — they're trusted external
oracles the implementation calls into.

DO NOT MODIFY — benchmark infrastructure.
-/

structure VerdictBundle where
  -- Base64 decoding
  charToBits           : Verdict.CharToBitsSig
  decode6Bits          : Verdict.Decode6BitsSig
  decodeBase64         : Verdict.DecodeBase64Sig
  parseX509Base64      : Verdict.ParseX509Base64Sig
  -- Issue-layer
  normalizeString      : Verdict.NormalizeStringSig
  verifySignature      : Verdict.VerifySignatureSig
  issuedByRaw          : Verdict.IssuedByRawSig
  -- Validator
  isSimplePath         : Verdict.IsSimplePathSig
  pathInBounds         : Verdict.PathInBoundsSig
  chainFromPath        : Verdict.ChainFromPathSig
  validateX509Base64   : Verdict.ValidateX509Base64Sig
  -- Chrome browser policy
  chromeCertVerifiedLeaf        : Verdict.ChromeCertVerifiedLeafSig
  chromeCertVerifiedIntermediate : Verdict.ChromeCertVerifiedIntermediateSig
  chromeCertVerifiedRoot        : Verdict.ChromeCertVerifiedRootSig
  chromeCheckAllNameConstraints : Verdict.ChromeCheckAllNameConstraintsSig
  chromeLikelyIssued            : Verdict.ChromeLikelyIssuedSig
  chromeValidChain              : Verdict.ChromeValidChainSig
  -- Firefox browser policy
  firefoxCertVerifiedLeaf        : Verdict.FirefoxCertVerifiedLeafSig
  firefoxCertVerifiedIntermediate : Verdict.FirefoxCertVerifiedIntermediateSig
  firefoxCertVerifiedRoot        : Verdict.FirefoxCertVerifiedRootSig
  firefoxCheckAllNameConstraints : Verdict.FirefoxCheckAllNameConstraintsSig
  firefoxLikelyIssued            : Verdict.FirefoxLikelyIssuedSig
  firefoxValidChain              : Verdict.FirefoxValidChainSig
  -- OpenSSL policy
  opensslValidLeaf              : Verdict.OpensslValidLeafSig
  opensslValidIntermediate      : Verdict.OpensslValidIntermediateSig
  opensslValidRoot              : Verdict.OpensslValidRootSig
  opensslCheckNameConstraints   : Verdict.OpensslCheckNameConstraintsSig
  opensslCheckHostname          : Verdict.OpensslCheckHostnameSig
  opensslLikelyIssued           : Verdict.OpensslLikelyIssuedSig
  opensslValidChain             : Verdict.OpensslValidChainSig
  -- Hex encoding (exec side only; `Verdict.specToHexUpper` is
  -- curator-given vocabulary and not part of the bundle).
  toHexUpper                    : Verdict.ToHexUpperSig
