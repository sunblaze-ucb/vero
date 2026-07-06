import Base58.Impl.Codec

/-!
# Base58.Bundle

Per-package implementation bundle for the `Base58` root package.
Collects all API signatures into one structure.

DO NOT MODIFY — benchmark infrastructure.
-/

structure Base58Bundle where
  decodeInt : Base58.DecodeIntSig
  encodeInt : Base58.EncodeIntSig
  encode    : Base58.EncodeSig
  decode    : Base58.DecodeSig
