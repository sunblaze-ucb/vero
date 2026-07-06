import Compression.Impl.Huffman
import Compression.Impl.BurrowsWheeler
import Compression.Impl.Lz77
import Compression.Impl.RunLengthEncoding
import Compression.Impl.CoordinateCompression

/-!
# Compression.Bundle

Per-package implementation bundle for the `Compression` root package.
Collects all API signatures into one structure.

DO NOT MODIFY — benchmark infrastructure.
-/

/-- Bundle holding one field per public API in the `Compression` package.
    Polymorphic fields use `∀ {α}` to carry the generic `CoordinateCompressor`
    APIs without fixing a concrete element type. -/
structure CompressionBundle where
  -- Huffman
  traverse_tree     : Compression.TraverseTreeSig
  build_tree        : Compression.BuildTreeSig
  -- BurrowsWheeler
  all_rotations     : Compression.AllRotationsSig
  bwt_transform     : Compression.BwtTransformSig
  reverse_bwt       : Compression.ReverseBwtSig
  -- Lz77
  lz77Compress      : Compression.LZ77CompressSig
  lz77Decompress    : Compression.LZ77DecompressSig
  -- RunLengthEncoding
  run_length_encode : Compression.RunLengthEncodeSig
  run_length_decode : Compression.RunLengthDecodeSig
  -- CoordinateCompression (polymorphic over element type)
  coordDecompress   : ∀ {α : Type _} [Ord α] [BEq α], Compression.CoordDecompressSig α
  coordCompress     : ∀ {α : Type _} [Ord α] [BEq α], Compression.CoordCompressSig α
